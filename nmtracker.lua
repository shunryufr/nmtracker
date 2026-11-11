_addon.name = 'NMTracker'
_addon.author = 'OpenAI'
_addon.version = '0.3.2-beta'
_addon.description = 'Suivi de NM par index hexadecimal TargetInfo (Windower 4 / Lua 5.1)'
_addon.commands = {'nm'}

local texts = require('texts')
local config = require('config')
local bit = require('bit')
local packets = require('packets')
require('tables')

-- Le paquet 0x058 doit utiliser le format Assist pour changer la cible
-- sans activer le verrouillage de cible. On ajoute aussi l'index de cible.
packets.raw_fields.incoming[0x058] = L{
    {ctype = 'unsigned int', label = 'Assist Id'},
    {ctype = 'unsigned int', label = 'Target Id'},
    {ctype = 'unsigned short', label = 'Assist Index'},
    {ctype = 'unsigned short', label = 'Target Index'},
}

local defaults = {
    window = {
        pos = {x = 350, y = 220},
        bg = {alpha = 210, red = 15, green = 18, blue = 24, visible = true},
        text = {
            size = 10, font = 'Consolas',
            alpha = 255, red = 235, green = 240, blue = 245,
            stroke = {width = 1, alpha = 220, red = 0, green = 0, blue = 0},
        },
        flags = {draggable = true, bold = false, italic = false},
        padding = 8,
    },
    visible = true,
    target_auto = false,
    scan_enabled = true,
    targets = {},
}

local settings = config.load(defaults)
settings.targets = settings.targets or {}
if settings.target_auto == nil then settings.target_auto = false end
if settings.scan_enabled == nil then settings.scan_enabled = true end

local window
local last_refresh = 0
local last_save = 0
local current_zone = nil
local clear_pending = false
local last_auto_target_id = nil
local last_auto_target_check = 0
local AUTO_TARGET_RANGE = 50
local AUTO_TARGET_INTERVAL = 0.5

-- Requete de mise a jour d'entite inspiree de ScanZone.
-- Une seule requete est en vol a la fois, avec un intervalle anti-spam.
local scan_inflight = nil
local scan_inflight_at = 0
local scan_inflight_zone = nil
local scan_last_request = 0
local scan_cursor = 0
local scan_zone_id = nil
local scan_zone_changed_at = 0
local SCAN_INTERVAL = 1.5
local SCAN_TIMEOUT = 3.0
local SCAN_POSITION_TTL = 12

local function msg(text)
    windower.add_to_chat(207, '[NMTracker] ' .. text)
end

local function normalize_hex(value)
    if not value then return nil end
    value = tostring(value):upper():gsub('^0X', '')
    if not value:match('^%x%x?%x?$') then return nil end
    local number = tonumber(value, 16)
    if not number or number < 0 or number > 0xFFF then return nil end
    return ('%03X'):format(number)
end

local function save_settings()
    -- Enregistre toute la configuration dans <global> pour tous les personnages.
    settings:save('all')
end

local function record_key(zone_id, hex)
    -- Les cles XML ne doivent pas contenir ':' ni commencer par un chiffre.
    return 'z' .. tostring(zone_id or 0) .. '_h' .. hex
end

local function hex_from_record_key(key)
    -- Accepte aussi les anciennes cles en memoire pour faciliter la migration.
    return tostring(key):match('_h([%x]+)$') or tostring(key):match('([^:]+)$') or tostring(key)
end

local function get_zone_id()
    local info = windower.ffxi.get_info()
    return info and info.zone or nil
end

local function get_player_mob()
    return windower.ffxi.get_mob_by_target('me')
end

-- Calcule l'angle avec la methode atan2 proposee, adaptee aux axes
-- horizontaux Windower/FFXI : X et Z (Y correspond a la hauteur).
local function angle_to(x, z)
    local player = get_player_mob()
    if not player or player.x == nil or player.z == nil
        or x == nil or z == nil then
        return nil
    end

    local dx = x - player.x
    local dz = z - player.z
    local atan2 = math.atan2
    local angle
    if atan2 then
        angle = math.deg(atan2(dz, dx))
    else
        -- Repli compatible si math.atan2 n'est pas expose.
        if dx == 0 then
            angle = (dz >= 0) and 90 or 270
        else
            angle = math.deg(math.atan(dz / dx))
            if dx < 0 then angle = angle + 180
            elseif dz < 0 then angle = angle + 360 end
        end
    end
    if angle < 0 then angle = angle + 360 end
    return angle
end

-- Direction inspiree de MobCompass (Feary/Addons).
-- MobCompass calcule l'angle depuis les coordonnees x_pos/y_pos
-- et traite explicitement les quadrants et les axes cardinaux.
local function direction_from_player(player, mob)
    if not player or not mob then
        return '??', nil
    end

    -- Les positions issues du scan 0x0E sont stockees en X, Y, Z,
    -- mais le paquet fournit les axes dans l'ordre X, Z, Y.
    -- Pour ces mobs, Z est le second axe horizontal ; Y est l'altitude.
    -- Les entites normales conservent le calcul MobCompass deja valide.
    local px, py, mx, my
    if mob.scanned then
        px = tonumber(player.x)
        py = tonumber(player.z)
        mx = tonumber(mob.x)
        my = tonumber(mob.z)
    else
        px = tonumber(player.x_pos or player.x)
        py = tonumber(player.y_pos or player.y)
        mx = tonumber(mob.x_pos or mob.x)
        my = tonumber(mob.y_pos or mob.y)
    end

    if not px or not py or not mx or not my then
        return '??', nil
    end

    -- Distance conservee avec les memes deux axes horizontaux.
    local dx = mx - px
    local dy = my - py
    local distance = math.sqrt(dx * dx + dy * dy)

    -- Methode calc_standard_angle de MobCompass, adaptee en local.
    local angle
    local delta_x = px - mx
    local delta_y = py - my

    if delta_y == 0 then
        if delta_x > 0 then
            angle = 90
        elseif delta_x < 0 then
            angle = 270
        else
            angle = 0
        end
    elseif delta_x == 0 then
        angle = (delta_y < 0) and 0 or 180
    else
        local base = math.deg(math.atan(delta_x / delta_y))
        if delta_x > 0 and delta_y > 0 then
            angle = base
        elseif delta_x > 0 and delta_y < 0 then
            angle = 180 + base
        elseif delta_x < 0 and delta_y < 0 then
            angle = 180 + base
        else -- delta_x < 0 and delta_y > 0
            angle = 360 + base
        end
    end

    angle = angle % 360
    local directions = {'N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW'}
    local index = math.floor((angle + 22.5) / 45) % 8 + 1

    -- Correction de 180 degres : toutes les directions etaient opposees.
    index = ((index - 1 + 4) % 8) + 1

    return directions[index], distance
end

local function get_hpp(mob, data)
    local hpp = mob and tonumber(mob.hpp) or nil
    if hpp == nil and data and data.scan_hpp ~= nil then
        if type(data.scan_hpp) == 'string' then
            hpp = string.byte(data.scan_hpp)
        else
            hpp = tonumber(data.scan_hpp)
        end
    end
    return hpp
end

local function color_line(line, color)
    -- Codes couleur pris en charge par le moteur texts de Windower.
    return ('\\cs(%s)%s\\cr'):format(color, line)
end

local function format_time(seconds)
    seconds = math.max(0, math.floor(seconds or 0))
    local hours = math.floor(seconds / 3600)
    local minutes = math.floor((seconds % 3600) / 60)
    local secs = seconds % 60
    if hours > 0 then
        return ('%02d:%02d:%02d'):format(hours, minutes, secs)
    end
    return ('%02d:%02d'):format(minutes, secs)
end

local function build_display()
    local now = os.time()
    local zone_id = get_zone_id()
    local player = get_player_mob()
    local mobs = windower.ffxi.get_mob_array() or {}
    local found = {}

    for _, mob in pairs(mobs) do
        if mob and mob.index and mob.id and mob.name and mob.is_npc then
            local key = ('%03X'):format(mob.index)
            local zone_key = record_key(get_zone_id(), key)
            if settings.targets[zone_key] then
                found[key] = mob
            end
        end
    end

    -- Si le mob n'est plus dans get_mob_array(), utiliser sa derniere
    -- position recue via la reponse 0x0E, uniquement pendant une courte duree.
    for stored_key, data in pairs(settings.targets) do
        if tostring(data.zone or 0) == tostring(zone_id or 0) then
            local key = hex_from_record_key(stored_key)
            if not found[key] and data.scan_has_position
                and data.scan_updated and (now - data.scan_updated) <= SCAN_POSITION_TTL then
                found[key] = {
                    -- Le paquet fournit les coordonnees dans l'ordre X, Z, Y.
                    -- Windower utilise X/Y pour le plan horizontal ; Z est conserve
                    -- comme troisieme axe, mais la boussole lit X/Y.
                    x = data.scan_x, y = data.scan_y, z = data.scan_z,
                    name = data.entity_name or data.name,
                    is_npc = true, scanned = true,
                }
            end
        end
    end

    local lines = {}
    lines[#lines + 1] = 'NM TRACKER  |  FFXI RETAIL'
    lines[#lines + 1] = ('Zone ID: %s'):format(zone_id and tostring(zone_id) or '?')
    lines[#lines + 1] = 'NOM (HEX)                         ETAT / DIRECTION'
    lines[#lines + 1] = '---------------------------------------------------'

    local keys = {}
    for stored_key, data in pairs(settings.targets) do
        if tostring(data.zone or 0) == tostring(zone_id or 0) then
            keys[#keys + 1] = hex_from_record_key(stored_key)
        end
    end
    table.sort(keys)

    if #keys == 0 then
        lines[#lines + 1] = 'Aucun NM configure.'
        lines[#lines + 1] = 'Commande: //nm add 123'
    else
        for _, key in ipairs(keys) do
            local data = settings.targets[record_key(zone_id, key)]
            local mob = found[key]
            -- Priorite au nom recu du jeu, puis au nom saisi manuellement.
            local name = (mob and mob.name) or data.entity_name or data.name or ('NM 0x' .. key)
            -- Toujours afficher le TargetInfo HEX pour identifier le PH suivi.
            local label = ('%-22s (%s)'):format(name:sub(1, 22), key)

            if mob then
                local hpp = get_hpp(mob, data)
                if hpp == 0 then
                    -- Mort : rouge, sans direction ni distance.
                    lines[#lines + 1] = color_line(
                        ('%-34s %s'):format(label, 'mort'),
                        '255,70,70'
                    )
                else
                    local dir, dist = direction_from_player(player, mob)
                    local source = mob.scanned and ' [scan]' or ''
 local line = ('%-34s %s %3d yalms%s'):format(
    label, dir,
    dist and math.floor(dist + 0.5) or 0, source
)
                    lines[#lines + 1] = color_line(line, '80,255,120')
                end
            elseif data.absent_since and data.absent_since > 0 then
                local elapsed = now - data.absent_since
                local respawn = tonumber(data.respawn) or 0
                local remaining = respawn > 0 and (respawn - elapsed) or 0
                local timer_text = respawn > 0
                    and ('respawn ' .. format_time(remaining))
                    or ('absent ' .. format_time(elapsed))
                -- Absent/non detecte : rouge, aucune direction ni distance.
                lines[#lines + 1] = color_line(
                    ('%-34s %s'):format(label, timer_text),
                    '255,70,70'
                )
            else
                -- Etat inconnu tant que le NM n'a jamais ete detecte.
                lines[#lines + 1] = color_line(
                    ('%-34s %s'):format(label, 'etat inconnu'),
                    '170,170,170'
                )
            end
        end
    end

    return table.concat(lines, '\n'), found
end

local function get_scan_targets()
    local zone_id = get_zone_id()
    local targets = {}
    for stored_key, data in pairs(settings.targets) do
        if tostring(data.zone or 0) == tostring(zone_id or 0) then
            local hex = hex_from_record_key(stored_key)
            local index = tonumber(hex, 16)
            if index and index >= 0 and index <= 0xFFF then
                targets[#targets + 1] = {hex = hex, index = index}
            end
        end
    end
    table.sort(targets, function(a, b) return a.hex < b.hex end)
    return targets
end


-- Selectionne le NM suivi le plus proche, uniquement dans les 50 yalms.
-- Utilise le format de paquet Assist (Assist Id/Index + Target Id/Index)
-- pour changer la cible sans verrouiller la cible ni engager le combat.
local function process_auto_target()
    if not settings.target_auto then
        last_auto_target_id = nil
        return
    end

    local now = os.clock()
    if (now - last_auto_target_check) < AUTO_TARGET_INTERVAL then
        return
    end
    last_auto_target_check = now

    local player = get_player_mob()
    if not player or not player.id or not player.index then return end

    local current_target = windower.ffxi.get_mob_by_target('t')
    local current_target_id = current_target and current_target.id or nil
    local mobs = windower.ffxi.get_mob_array() or {}
    local zone_id = get_zone_id()
    local nearest = nil
    local nearest_distance = AUTO_TARGET_RANGE

    for _, mob in pairs(mobs) do
        if mob and mob.id and mob.index and mob.is_npc and mob.name then
            local hex = ('%03X'):format(mob.index)
            local key = record_key(zone_id, hex)
            if settings.targets[key] then
                local _, distance = direction_from_player(player, mob)
                if distance and distance <= AUTO_TARGET_RANGE
                    and (not nearest or distance < nearest_distance) then
                    nearest = mob
                    nearest_distance = distance
                end
            end
        end
    end

    if not nearest then
        -- On ne deselectionne pas une cible deja verrouillee.
        last_auto_target_id = nil
        return
    end

    if current_target_id == nearest.id or last_auto_target_id == nearest.id then
        return
    end

    local ok, err = pcall(function()
        packets.inject(packets.new('incoming', 0x058, {
            ['Assist Id'] = player.id,
            ['Target Id'] = nearest.id,
            ['Assist Index'] = player.index,
            ['Target Index'] = nearest.index,
        }))
    end)

    if ok then
        last_auto_target_id = nearest.id
        msg(('Cible automatique: %s (0x%03X) a %d yalms.'):format(
            nearest.name, nearest.index, math.floor(nearest_distance + 0.5)
        ))
    else
        msg('Erreur ciblage automatique: ' .. tostring(err))
        settings.target_auto = false
        save_settings()
    end
end

local function send_scan_request(target_index)
    -- Structure reprise du fichier ScanZone fourni : paquet sortant 0x16.
    local packet = string.char(
        0x16, 0x08, 0x00, 0x00,
        target_index % 256, math.floor(target_index / 256),
        0x00, 0x00
    )
    windower.packets.inject_outgoing(0x16, packet)
end

local function process_scan_queue()
    if not settings.scan_enabled then
        scan_inflight = nil
        scan_inflight_zone = nil
        return
    end

    local now = os.clock()
    local zone_id = get_zone_id()

    -- A chaque changement de zone, on repart du debut de la liste sauvegardee
    -- pour cette zone. On laisse aussi un court delai aux anciennes reponses.
    if scan_zone_id ~= zone_id then
        scan_zone_id = zone_id
        scan_inflight = nil
        scan_inflight_zone = nil
        scan_cursor = 0
        scan_last_request = 0
        scan_zone_changed_at = now
        return
    end

    if (now - scan_zone_changed_at) < SCAN_INTERVAL then
        return
    end

    if scan_inflight and (now - scan_inflight_at) >= SCAN_TIMEOUT then
        scan_inflight = nil
        scan_inflight_zone = nil
    end
    if scan_inflight or (now - scan_last_request) < SCAN_INTERVAL then
        return
    end

    local targets = get_scan_targets()
    if #targets == 0 then return end

    scan_cursor = (scan_cursor % #targets) + 1
    local target = targets[scan_cursor]
    scan_inflight = target.index
    scan_inflight_zone = zone_id
    scan_inflight_at = now
    scan_last_request = now

    local ok, err = pcall(send_scan_request, target.index)
    if not ok then
        scan_inflight = nil
        scan_inflight_zone = nil
        msg('Erreur requete scan: ' .. tostring(err))
    end
end

local function handle_scan_response(original)
    local zone_id = get_zone_id()
    if not settings.scan_enabled or not scan_inflight or not original
        or scan_inflight_zone ~= zone_id then
        return
    end

    local ok, target_index, updatemask, entity_id = pcall(function()
        return original:unpack('h', 0x09),
            original:unpack('b', 0x0B),
            original:unpack('I', 0x05)
    end)
    if not ok or target_index ~= scan_inflight then return end

    local hex = ('%03X'):format(target_index)
    local key = record_key(zone_id, hex)
    local data = settings.targets[key]
    scan_inflight = nil
    scan_inflight_zone = nil
    if not data then return end

    if entity_id then data.entity_id = entity_id end
    if updatemask and bit.band(updatemask, 0x08) == 0x08 then
        local name = ''
        for i = 1, math.max(0, #original - 0x34) do
            local char_ok, value = pcall(function()
                return original:unpack('c', 0x34 + i)
            end)
            if char_ok and value and value ~= 0 then
                name = name .. string.char(value)
            end
        end
        name = name:gsub('%z+$', '')
        if name ~= '' then data.entity_name = name end
    end

    if updatemask and bit.band(updatemask, 0x01) == 0x01 then
        local pos_ok, x, z, y = pcall(function()
            return original:unpack('fff', 0x0D)
        end)
        if pos_ok and x and z and y then
            data.scan_x, data.scan_z, data.scan_y = x, z, y
            data.scan_has_position = true
            data.scan_updated = os.time()
        end
    end

    if updatemask and bit.band(updatemask, 0x04) == 0x04 then
        local status_ok, hpp, animation, status = pcall(function()
            return original:unpack('ccc', 0x1F)
        end)
        if status_ok then
            data.scan_hpp = hpp
            data.scan_status = status
        end
    end

    if data.scan_has_position then
        data.last_seen = os.time()
        data.absent_since = 0
    end
end

local function refresh()
    if not window then return end

    local now = os.time()
    local zone_id = get_zone_id()
    if current_zone ~= zone_id then
        current_zone = zone_id
        -- Les index sont propres à une zone : on ne marque pas les NM
        -- comme disparus pendant un changement de zone.
        for _, data in pairs(settings.targets) do
            if tostring(data.zone or 0) == tostring(zone_id or 0) then
                data.absent_since = 0
                data.last_seen = 0
            end
        end
    end

    local display, found = build_display()
    window:text(display)

    local changed = false
    for stored_key, data in pairs(settings.targets) do
        if tostring(data.zone or 0) == tostring(zone_id or 0) then
            local hex = hex_from_record_key(stored_key)
            if found[hex] then
                if data.absent_since and data.absent_since > 0 then
                    data.absent_since = 0
                    changed = true
                end
                if not data.last_seen or data.last_seen == 0 then
                    data.last_seen = now
                    changed = true
                end
            elseif data.last_seen and data.last_seen > 0
                and (not data.absent_since or data.absent_since == 0) then
                data.absent_since = now
                changed = true
            end
        end
    end

    if changed or now - last_save >= 30 then
        save_settings()
        last_save = now
    end
end

local function show_window()
    if window then window:show() end
    settings.visible = true
    save_settings()
end

local function hide_window()
    if window then window:hide() end
    settings.visible = false
    save_settings()
end

local function help()
    msg('Commandes:')
    msg("//nm add 123 [nom]  - ajoute l'index de la zone actuelle")
    msg('//nm remove 123     - retire un NM')
    msg('//nm respawn 123 60 - respawn en minutes')
    msg('//nm name 123 Nom  - definit le nom affiche')
    msg('//nm list           - liste les Hex ID suivis')
    msg('//nm clear          - vide toute la liste (confirmation requise)')
    msg('//nm clear confirm  - confirme le vidage de la liste')
    msg('//nm targetauto on  - active le ciblage auto a 50 yalms max')
    msg('//nm targetauto off - desactive le ciblage automatique')
    msg('//nm targetauto status - affiche son etat')
    msg('//nm scanzone on    - active les scans ScanZone')
    msg('//nm scanzone off   - desactive les scans ScanZone')
    msg('//nm scanzone status - affiche son etat')
    msg('//nm show | hide    - affiche/cache la fenetre')
end

windower.register_event('addon command', function(command, ...)
    command = (command or ''):lower()
    local args = {...}

    if command == 'add' then
        local hex = normalize_hex(args[1])
        if not hex then
            msg('Format attendu: //nm add 123 [nom]')
            return
        end
        local zone_id = get_zone_id()
        if not zone_id then
            msg('Impossible de lire la zone actuelle.')
            return
        end
        local key = record_key(zone_id, hex)
        if settings.targets[key] then
            msg('0x' .. hex .. ' est deja suivi dans cette zone.')
            return
        end
        local name = table.concat(args, ' ', 2)
        if name == '' then name = 'NM 0x' .. hex end
        settings.targets[key] = {
            zone = zone_id,
            name = name,
            respawn = 0,
            last_seen = 0,
            absent_since = 0,
        }
        save_settings()
        msg('0x' .. hex .. ' ajoute: ' .. name)

    elseif command == 'remove' then
        local hex = normalize_hex(args[1])
        local zone_id = get_zone_id()
        local removed = false

        if hex then
            -- Supprime aussi les anciennes cles de configuration (migration).
            -- Certaines entrees peuvent ne pas utiliser z<zone>_h<hex>.
            for stored_key, data in pairs(settings.targets) do
                if tostring(data.zone or 0) == tostring(zone_id or 0)
                    and hex_from_record_key(stored_key):upper() == hex then
                    settings.targets[stored_key] = nil
                    removed = true
                end
            end
        end

        if removed then
            save_settings()
            msg('0x' .. hex .. ' retire de cette zone.')
        else
            msg('Hex ID inconnu dans cette zone. Utilise //nm list.')
        end

    elseif command == 'respawn' then
        local hex = normalize_hex(args[1])
        local minutes = tonumber(args[2])
        local key = hex and record_key(get_zone_id(), hex)
        if key and settings.targets[key] and minutes and minutes >= 0 then
            settings.targets[key].respawn = math.floor(minutes * 60)
            save_settings()
            msg('Respawn de 0x' .. hex .. ' defini a ' .. minutes .. ' min.')
        else
            msg('Format: //nm respawn 123 60')
        end

    elseif command == 'name' then
        local hex = normalize_hex(args[1])
        local name = table.concat(args, ' ', 2)
        local key = hex and record_key(get_zone_id(), hex)
        if key and settings.targets[key] and name ~= '' then
            settings.targets[key].name = name
            save_settings()
            msg('Nom de 0x' .. hex .. ' modifie.')
        else
            msg('Format: //nm name 123 Nom du NM')
        end

    elseif command == 'targetauto' then
        local action = (args[1] or 'status'):lower()
        if action == 'on' then
            settings.target_auto = true
            last_auto_target_id = nil
            save_settings()
            msg('Ciblage automatique active (NM suivis a 50 yalms maximum).')
        elseif action == 'off' then
            settings.target_auto = false
            last_auto_target_id = nil
            save_settings()
            msg('Ciblage automatique desactive.')
        elseif action == 'status' then
            msg('Ciblage automatique: ' .. (settings.target_auto and 'ACTIVE' or 'DESACTIVE')
                .. ' | portee: ' .. AUTO_TARGET_RANGE .. ' yalms.')
        else
            msg('Format: //nm targetauto on | off | status')
        end

    elseif command == 'scanzone' then
        local action = (args[1] or 'status'):lower()
        if action == 'on' then
            settings.scan_enabled = true
            scan_inflight = nil
            scan_inflight_zone = nil
            scan_last_request = 0
            scan_cursor = 0
            save_settings()
            msg('ScanZone active. Les requetes de scan reprennent.')
        elseif action == 'off' then
            settings.scan_enabled = false
            scan_inflight = nil
            scan_inflight_zone = nil
            save_settings()
            msg('ScanZone desactive. Aucun nouveau scan ne sera envoye.')
        elseif action == 'status' then
            msg('ScanZone: ' .. (settings.scan_enabled and 'ACTIF' or 'DESACTIVE') .. '.')
        else
            msg('Format: //nm scanzone on | off | status')
        end

    elseif command == 'clear' then
        local action = (args[1] or ''):lower()
        if action == 'cancel' then
            clear_pending = false
            msg('Vidage annule. La liste est conservee.')
        elseif action == 'confirm' then
            if not clear_pending then
                msg('Aucun vidage en attente. Utilise //nm clear d abord.')
                return
            end
            settings.targets = {}
            clear_pending = false
            scan_inflight = nil
            scan_inflight_zone = nil
            scan_cursor = 0
            save_settings()
            msg('Liste complete des NM et timers effaces.')
        else
            clear_pending = true
            msg('Attention : cela effacera tous les NM et timers.')
            msg('Tape //nm clear confirm pour confirmer, ou //nm clear cancel pour annuler.')
        end

    elseif command == 'list' then
        local count = 0
        for stored_key, data in pairs(settings.targets) do
            count = count + 1
            local hex = hex_from_record_key(stored_key)
            msg(('Zone %s | 0x%s - %s - respawn %s'):format(
                tostring(data.zone or '?'), hex, data.name or 'NM',
                format_time(data.respawn or 0)
            ))
        end
        if count == 0 then msg('Aucun NM configure.') end

    elseif command == 'show' then
        show_window()
    elseif command == 'hide' then
        hide_window()
    elseif command == 'help' or command == nil or command == '' then
        help()
    else
        help()
    end
end)

-- Creation simple du texte : on evite de lier directement la fenetre
-- a la configuration globale pendant le diagnostic d'affichage.
local window_ok, window_or_error = pcall(function()
    local w = texts.new(
        'NM TRACKER | FFXI RETAIL\\nInitialisation...\\nUtilise //nm help',
        settings.window
    )
    w:draggable(true)
    w:show()
    return w
end)

if not window_ok then
    msg('ERREUR creation fenetre: ' .. tostring(window_or_error))
    return
end

window = window_or_error

windower.register_event('incoming chunk', function(id, original, modified, injected)
    if id == 0x0E then
        handle_scan_response(original)
    end
end)

windower.register_event('prerender', function()
    process_scan_queue()
    process_auto_target()
    local now = os.time()
    if now ~= last_refresh then
        last_refresh = now
        refresh()
    end
end)

windower.register_event('load', function()
    current_zone = get_zone_id()
    scan_zone_id = current_zone
    scan_zone_changed_at = os.clock()
    refresh()
    if settings.visible then show_window() else hide_window() end
end)

windower.register_event('unload', function()
    save_settings()
    if window then window:destroy() end
end)

if settings.visible == false then
    window:hide()
else
    window:show()
end

refresh()
msg('Charge v0.3.2-beta. ScanZone: ' .. (settings.scan_enabled and 'ON' or 'OFF') .. ' | Ciblage auto: ' .. (settings.target_auto and 'ON' or 'OFF') .. '. //nm help')
