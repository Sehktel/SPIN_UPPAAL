MACHINE FormalSpecification
-- ProB модель формальной спецификации системы управления
-- Автор: Senior Developer
-- Описание: Формальная спецификация системы с инвариантами и операциями

SETS
    -- Множества состояний системы
    PUMP_STATE = {STOPPED, STARTING, RUNNING, STOPPING, ERROR, MAINTENANCE};
    VALVE_STATE = {CLOSED, OPENING, OPEN, CLOSING, ERROR_VALVE, MAINTENANCE_VALVE};
    SENSOR_STATE = {OK, CALIBRATING, ERROR_SENSOR, OFFLINE};
    SYSTEM_MODE = {INITIALIZATION, OPERATIONAL, EMERGENCY, SHUTDOWN, MAINTENANCE_MODE};
    PRIORITY_LEVEL = {LOW, MEDIUM, HIGH, CRITICAL};

VARIABLES
    -- Основные переменные системы
    pump1_state, pump2_state,
    valve1_state, valve2_state,
    temp_sensor_state, pressure_sensor_state, humidity_sensor_state,
    system_mode, emergency_active, maintenance_mode,
    pump1_pressure, pump2_pressure,
    tank1_level, tank2_level,
    system_health, error_count,
    last_maintenance, uptime,
    active_alarms, pending_tasks

INVARIANT
    -- Инварианты безопасности
    pump1_state : PUMP_STATE &
    pump2_state : PUMP_STATE &
    valve1_state : VALVE_STATE &
    valve2_state : VALVE_STATE &
    temp_sensor_state : SENSOR_STATE &
    pressure_sensor_state : SENSOR_STATE &
    humidity_sensor_state : SENSOR_STATE &
    system_mode : SYSTEM_MODE &
    emergency_active : BOOL &
    maintenance_mode : BOOL &
    pump1_pressure : NAT &
    pump2_pressure : NAT &
    tank1_level : NAT &
    tank2_level : NAT &
    system_health : NAT &
    error_count : NAT &
    last_maintenance : NAT &
    uptime : NAT &
    active_alarms : NAT &
    pending_tasks : NAT &
    
    -- Ограничения безопасности
    pump1_pressure <= 100 &
    pump2_pressure <= 100 &
    tank1_level <= 1000 &
    tank2_level <= 1000 &
    system_health <= 100 &
    error_count <= 10 &
    active_alarms <= 5 &
    pending_tasks <= 20 &
    
    -- Логические ограничения
    (emergency_active = TRUE => system_mode = EMERGENCY) &
    (maintenance_mode = TRUE => system_mode = MAINTENANCE_MODE) &
    (pump1_state = RUNNING => pump1_pressure > 0) &
    (pump2_state = RUNNING => pump2_pressure > 0) &
    (valve1_state = OPEN => tank1_level > 0) &
    (valve2_state = OPEN => tank2_level > 0) &
    
    -- Взаимные исключения
    ~(pump1_state = RUNNING & pump2_state = RUNNING) |
    (pump1_state = RUNNING & pump2_state = RUNNING & system_mode = MAINTENANCE_MODE) &
    
    -- Состояния датчиков
    (temp_sensor_state = ERROR_SENSOR => system_health < 80) &
    (pressure_sensor_state = ERROR_SENSOR => system_health < 80) &
    (humidity_sensor_state = ERROR_SENSOR => system_health < 80)

INITIALISATION
    pump1_state := STOPPED &
    pump2_state := STOPPED &
    valve1_state := CLOSED &
    valve2_state := CLOSED &
    temp_sensor_state := OK &
    pressure_sensor_state := OK &
    humidity_sensor_state := OK &
    system_mode := INITIALIZATION &
    emergency_active := FALSE &
    maintenance_mode := FALSE &
    pump1_pressure := 0 &
    pump2_pressure := 0 &
    tank1_level := 500 &
    tank2_level := 300 &
    system_health := 100 &
    error_count := 0 &
    last_maintenance := 0 &
    uptime := 0 &
    active_alarms := 0 &
    pending_tasks := 0

OPERATIONS
    -- Операция запуска насоса 1
    StartPump1 = 
        PRE pump1_state = STOPPED &
             system_mode = OPERATIONAL &
             emergency_active = FALSE &
             temp_sensor_state = OK &
             pressure_sensor_state = OK &
             tank1_level > 100
        THEN
            pump1_state := STARTING &
            pending_tasks := pending_tasks + 1
        END;
    
    -- Операция запуска насоса 2
    StartPump2 = 
        PRE pump2_state = STOPPED &
             system_mode = OPERATIONAL &
             emergency_active = FALSE &
             temp_sensor_state = OK &
             pressure_sensor_state = OK &
             tank2_level > 100
        THEN
            pump2_state := STARTING &
            pending_tasks := pending_tasks + 1
        END;
    
    -- Операция остановки насоса 1
    StopPump1 = 
        PRE pump1_state : {STARTING, RUNNING, ERROR}
        THEN
            pump1_state := STOPPING &
            pump1_pressure := 0 &
            pending_tasks := pending_tasks - 1
        END;
    
    -- Операция остановки насоса 2
    StopPump2 = 
        PRE pump2_state : {STARTING, RUNNING, ERROR}
        THEN
            pump2_state := STOPPING &
            pump2_pressure := 0 &
            pending_tasks := pending_tasks - 1
        END;
    
    -- Операция открытия клапана 1
    OpenValve1 = 
        PRE valve1_state = CLOSED &
             tank1_level > 0 &
             system_mode = OPERATIONAL
        THEN
            valve1_state := OPENING &
            pending_tasks := pending_tasks + 1
        END;
    
    -- Операция закрытия клапана 1
    CloseValve1 = 
        PRE valve1_state = OPEN
        THEN
            valve1_state := CLOSING &
            pending_tasks := pending_tasks - 1
        END;
    
    -- Операция открытия клапана 2
    OpenValve2 = 
        PRE valve2_state = CLOSED &
             tank2_level > 0 &
             system_mode = OPERATIONAL
        THEN
            valve2_state := OPENING &
            pending_tasks := pending_tasks + 1
        END;
    
    -- Операция закрытия клапана 2
    CloseValve2 = 
        PRE valve2_state = OPEN
        THEN
            valve2_state := CLOSING &
            pending_tasks := pending_tasks - 1
        END;
    
    -- Операция аварийной остановки
    EmergencyStop = 
        PRE emergency_active = FALSE
        THEN
            emergency_active := TRUE &
            system_mode := EMERGENCY &
            pump1_state := STOPPING &
            pump2_state := STOPPING &
            valve1_state := CLOSING &
            valve2_state := CLOSING &
            pump1_pressure := 0 &
            pump2_pressure := 0 &
            active_alarms := active_alarms + 1
        END;
    
    -- Операция сброса аварии
    ResetEmergency = 
        PRE emergency_active = TRUE &
             pump1_state = STOPPED &
             pump2_state = STOPPED &
             valve1_state = CLOSED &
             valve2_state = CLOSED
        THEN
            emergency_active := FALSE &
            system_mode := OPERATIONAL &
            active_alarms := active_alarms - 1
        END;
    
    -- Операция перехода в режим обслуживания
    EnterMaintenance = 
        PRE system_mode = OPERATIONAL &
             emergency_active = FALSE
        THEN
            maintenance_mode := TRUE &
            system_mode := MAINTENANCE_MODE &
            pump1_state := STOPPING &
            pump2_state := STOPPING &
            valve1_state := CLOSING &
            valve2_state := CLOSING
        END;
    
    -- Операция выхода из режима обслуживания
    ExitMaintenance = 
        PRE system_mode = MAINTENANCE_MODE &
             pump1_state = STOPPED &
             pump2_state = STOPPED &
             valve1_state = CLOSED &
             valve2_state = CLOSED
        THEN
            maintenance_mode := FALSE &
            system_mode := OPERATIONAL &
            last_maintenance := uptime
        END;
    
    -- Операция калибровки датчика температуры
    CalibrateTempSensor = 
        PRE temp_sensor_state = OK &
             system_mode = OPERATIONAL
        THEN
            temp_sensor_state := CALIBRATING &
            pending_tasks := pending_tasks + 1
        END;
    
    -- Операция завершения калибровки датчика температуры
    CompleteTempCalibration = 
        PRE temp_sensor_state = CALIBRATING
        THEN
            temp_sensor_state := OK &
            pending_tasks := pending_tasks - 1
        END;
    
    -- Операция обработки ошибки датчика
    HandleSensorError = 
        PRE temp_sensor_state = ERROR_SENSOR |
             pressure_sensor_state = ERROR_SENSOR |
             humidity_sensor_state = ERROR_SENSOR
        THEN
            IF temp_sensor_state = ERROR_SENSOR THEN
                temp_sensor_state := OFFLINE
            END &
            IF pressure_sensor_state = ERROR_SENSOR THEN
                pressure_sensor_state := OFFLINE
            END &
            IF humidity_sensor_state = ERROR_SENSOR THEN
                humidity_sensor_state := OFFLINE
            END &
            error_count := error_count + 1 &
            system_health := max(0, system_health - 10) &
            active_alarms := active_alarms + 1
        END;
    
    -- Операция восстановления датчика
    RecoverSensor = 
        PRE temp_sensor_state = OFFLINE |
             pressure_sensor_state = OFFLINE |
             humidity_sensor_state = OFFLINE
        THEN
            IF temp_sensor_state = OFFLINE THEN
                temp_sensor_state := OK
            END &
            IF pressure_sensor_state = OFFLINE THEN
                pressure_sensor_state := OK
            END &
            IF humidity_sensor_state = OFFLINE THEN
                humidity_sensor_state := OK
            END &
            system_health := min(100, system_health + 5) &
            active_alarms := max(0, active_alarms - 1)
        END;
    
    -- Операция обновления состояния системы
    UpdateSystemState = 
        PRE system_mode = OPERATIONAL
        THEN
            -- Обновление давления насосов
            IF pump1_state = RUNNING THEN
                pump1_pressure := min(100, pump1_pressure + 5)
            END &
            IF pump2_state = RUNNING THEN
                pump2_pressure := min(100, pump2_pressure + 5)
            END &
            
            -- Обновление уровня в резервуарах
            IF valve1_state = OPEN THEN
                tank1_level := max(0, tank1_level - 2)
            END &
            IF valve2_state = OPEN THEN
                tank2_level := max(0, tank2_level - 1)
            END &
            
            -- Обновление времени работы
            uptime := uptime + 1 &
            
            -- Обновление здоровья системы
            IF error_count > 0 THEN
                system_health := max(0, system_health - 1)
            END
        END;
    
    -- Операция очистки ошибок
    ClearErrors = 
        PRE error_count > 0 &
             system_mode = OPERATIONAL
        THEN
            error_count := 0 &
            system_health := min(100, system_health + 10)
        END

END


