-- Специализированная модель промышленного управления для ProB
-- Моделирует систему управления промышленным процессом с безопасностью и мониторингом

MACHINE IndustrialControlSystem
SETS
    -- Типы устройств
    DEVICE_TYPE = {PUMP, VALVE, SENSOR, ACTUATOR, MOTOR, HEATER, COOLER, CONVEYOR};
    
    -- Типы сигналов
    SIGNAL_TYPE = {ANALOG, DIGITAL, PULSE, FREQUENCY, CURRENT, VOLTAGE};
    
    -- Состояния устройств
    DEVICE_STATE = {OFF, ON, RUNNING, STOPPED, ERROR, MAINTENANCE, CALIBRATION};
    
    -- Уровни приоритета
    PRIORITY_LEVEL = {LOW, MEDIUM, HIGH, CRITICAL, EMERGENCY};
    
    -- Типы аварийных ситуаций
    ALARM_TYPE = {HIGH_TEMP, LOW_TEMP, HIGH_PRESSURE, LOW_PRESSURE, HIGH_LEVEL, LOW_LEVEL, 
                  OVERFLOW, UNDERFLOW, OVERSPEED, UNDERTORQUE, COMMUNICATION_FAILURE, POWER_FAILURE};
    
    -- Режимы работы
    OPERATION_MODE = {MANUAL, AUTOMATIC, SEMI_AUTO, EMERGENCY, MAINTENANCE, CALIBRATION};
    
    -- Статусы операций
    OPERATION_STATUS = {PENDING, IN_PROGRESS, COMPLETED, FAILED, CANCELLED, TIMEOUT};
    
    -- Типы пользователей
    USER_TYPE = {OPERATOR, SUPERVISOR, ENGINEER, ADMINISTRATOR, MAINTENANCE};

VARIABLES
    -- Основные устройства системы
    devices : DEVICE_TYPE <-> DEVICE_STATE;
    
    -- Сигналы от датчиков
    sensor_signals : SIGNAL_TYPE <-> NATURAL;
    
    -- Управляющие сигналы
    control_signals : DEVICE_TYPE <-> NATURAL;
    
    -- Состояние системы
    system_mode : OPERATION_MODE;
    
    -- Активные аварийные сигналы
    active_alarms : ALARM_TYPE <-> PRIORITY_LEVEL;
    
    -- Текущие операции
    current_operations : DEVICE_TYPE <-> OPERATION_STATUS;
    
    -- Пользователи системы
    active_users : USER_TYPE <-> BOOL;
    
    -- Таймеры и счетчики
    device_timers : DEVICE_TYPE <-> NATURAL;
    operation_timers : DEVICE_TYPE <-> NATURAL;
    alarm_counters : ALARM_TYPE <-> NATURAL;
    
    -- Статистика работы
    total_operations : NATURAL;
    successful_operations : NATURAL;
    failed_operations : NATURAL;
    maintenance_count : NATURAL;
    
    -- Параметры безопасности
    safety_system_active : BOOL;
    emergency_stop_active : BOOL;
    safety_interlocks : DEVICE_TYPE <-> BOOL;
    
    -- Конфигурация системы
    device_configs : DEVICE_TYPE <-> NATURAL;
    alarm_thresholds : ALARM_TYPE <-> NATURAL;
    operation_limits : DEVICE_TYPE <-> NATURAL;

INVARIANT
    -- Инварианты безопасности
    safety_system_active = TRUE;
    emergency_stop_active = FALSE;
    
    -- Инварианты устройств
    devices : DEVICE_TYPE <-> DEVICE_STATE;
    control_signals : DEVICE_TYPE <-> NATURAL;
    
    -- Инварианты сигналов
    sensor_signals : SIGNAL_TYPE <-> NATURAL;
    
    -- Инварианты операций
    current_operations : DEVICE_TYPE <-> OPERATION_STATUS;
    
    -- Инварианты аварийных сигналов
    active_alarms : ALARM_TYPE <-> PRIORITY_LEVEL;
    
    -- Инварианты пользователей
    active_users : USER_TYPE <-> BOOL;
    
    -- Инварианты таймеров
    device_timers : DEVICE_TYPE <-> NATURAL;
    operation_timers : DEVICE_TYPE <-> NATURAL;
    alarm_counters : ALARM_TYPE <-> NATURAL;
    
    -- Инварианты статистики
    total_operations : NATURAL;
    successful_operations : NATURAL;
    failed_operations : NATURAL;
    maintenance_count : NATURAL;
    
    -- Инварианты безопасности
    safety_interlocks : DEVICE_TYPE <-> BOOL;
    
    -- Инварианты конфигурации
    device_configs : DEVICE_TYPE <-> NATURAL;
    alarm_thresholds : ALARM_TYPE <-> NATURAL;
    operation_limits : DEVICE_TYPE <-> NATURAL;
    
    -- Логические инварианты
    successful_operations + failed_operations <= total_operations;
    (FORALL (device : DEVICE_TYPE) : 
        device : dom(devices) => device : dom(control_signals));
    (FORALL (alarm : ALARM_TYPE) : 
        alarm : dom(active_alarms) => alarm : dom(alarm_thresholds));

INITIALISATION
    -- Инициализация устройств
    devices := {};
    control_signals := {};
    sensor_signals := {};
    
    -- Инициализация состояния системы
    system_mode := MANUAL;
    
    -- Инициализация аварийных сигналов
    active_alarms := {};
    
    -- Инициализация операций
    current_operations := {};
    
    -- Инициализация пользователей
    active_users := {};
    
    -- Инициализация таймеров
    device_timers := {};
    operation_timers := {};
    alarm_counters := {};
    
    -- Инициализация статистики
    total_operations := 0;
    successful_operations := 0;
    failed_operations := 0;
    maintenance_count := 0;
    
    -- Инициализация безопасности
    safety_system_active := TRUE;
    emergency_stop_active := FALSE;
    safety_interlocks := {};
    
    -- Инициализация конфигурации
    device_configs := {};
    alarm_thresholds := {};
    operation_limits := {};

OPERATIONS
    -- Запуск устройства
    StartDevice(device) = 
        PRE device : DEVICE_TYPE & 
             device : dom(devices) & 
             devices(device) = OFF &
             safety_interlocks(device) = TRUE
        THEN
            devices(device) := RUNNING;
            control_signals(device) := 1;
            current_operations(device) := IN_PROGRESS;
            operation_timers(device) := 0;
            total_operations := total_operations + 1
        END;
    
    -- Остановка устройства
    StopDevice(device) = 
        PRE device : DEVICE_TYPE & 
             device : dom(devices) & 
             devices(device) = RUNNING
        THEN
            devices(device) := STOPPED;
            control_signals(device) := 0;
            current_operations(device) := COMPLETED;
            successful_operations := successful_operations + 1
        END;
    
    -- Аварийная остановка
    EmergencyStop = 
        PRE emergency_stop_active = FALSE
        THEN
            emergency_stop_active := TRUE;
            -- Остановка всех устройств
            devices := {device | device : DEVICE_TYPE & device : dom(devices) & devices(device) = RUNNING} * {STOPPED};
            control_signals := {device | device : DEVICE_TYPE & device : dom(devices) & devices(device) = STOPPED} * {0};
            current_operations := {device | device : DEVICE_TYPE & device : dom(devices) & current_operations(device) = IN_PROGRESS} * {FAILED};
            system_mode := EMERGENCY
        END;
    
    -- Сброс аварийной остановки
    ResetEmergencyStop = 
        PRE emergency_stop_active = TRUE & 
             safety_system_active = TRUE
        THEN
            emergency_stop_active := FALSE;
            system_mode := MANUAL
        END;
    
    -- Изменение режима работы
    ChangeOperationMode(new_mode) = 
        PRE new_mode : OPERATION_MODE & 
             new_mode /= EMERGENCY &
             emergency_stop_active = FALSE
        THEN
            system_mode := new_mode
        END;
    
    -- Добавление устройства
    AddDevice(device, initial_state) = 
        PRE device : DEVICE_TYPE & 
             initial_state : DEVICE_STATE &
             device /: dom(devices)
        THEN
            devices(device) := initial_state;
            control_signals(device) := 0;
            device_timers(device) := 0;
            operation_timers(device) := 0;
            safety_interlocks(device) := TRUE;
            device_configs(device) := 0;
            operation_limits(device) := 100
        END;
    
    -- Удаление устройства
    RemoveDevice(device) = 
        PRE device : DEVICE_TYPE & 
             device : dom(devices) &
             devices(device) = OFF
        THEN
            devices := {device} <<| devices;
            control_signals := {device} <<| control_signals;
            device_timers := {device} <<| device_timers;
            operation_timers := {device} <<| operation_timers;
            safety_interlocks := {device} <<| safety_interlocks;
            device_configs := {device} <<| device_configs;
            operation_limits := {device} <<| operation_limits;
            current_operations := {device} <<| current_operations
        END;
    
    -- Установка аварийного порога
    SetAlarmThreshold(alarm_type, threshold) = 
        PRE alarm_type : ALARM_TYPE & 
             threshold : NATURAL
        THEN
            alarm_thresholds(alarm_type) := threshold
        END;
    
    -- Активация аварийного сигнала
    ActivateAlarm(alarm_type, priority) = 
        PRE alarm_type : ALARM_TYPE & 
             priority : PRIORITY_LEVEL &
             alarm_type /: dom(active_alarms)
        THEN
            active_alarms(alarm_type) := priority;
            alarm_counters(alarm_type) := alarm_counters(alarm_type) + 1
        END;
    
    -- Деактивация аварийного сигнала
    DeactivateAlarm(alarm_type) = 
        PRE alarm_type : ALARM_TYPE & 
             alarm_type : dom(active_alarms)
        THEN
            active_alarms := {alarm_type} <<| active_alarms
        END;
    
    -- Обновление сигнала датчика
    UpdateSensorSignal(signal_type, value) = 
        PRE signal_type : SIGNAL_TYPE & 
             value : NATURAL
        THEN
            sensor_signals(signal_type) := value
        END;
    
    -- Установка управляющего сигнала
    SetControlSignal(device, value) = 
        PRE device : DEVICE_TYPE & 
             value : NATURAL &
             device : dom(devices) &
             value <= operation_limits(device)
        THEN
            control_signals(device) := value
        END;
    
    -- Запуск операции
    StartOperation(device, operation_type) = 
        PRE device : DEVICE_TYPE & 
             operation_type : OPERATION_STATUS &
             device : dom(devices) &
             current_operations(device) = COMPLETED
        THEN
            current_operations(device) := operation_type;
            operation_timers(device) := 0;
            total_operations := total_operations + 1
        END;
    
    -- Завершение операции
    CompleteOperation(device, success) = 
        PRE device : DEVICE_TYPE & 
             success : BOOL &
             device : dom(devices) &
             current_operations(device) = IN_PROGRESS
        THEN
            IF success = TRUE THEN
                current_operations(device) := COMPLETED;
                successful_operations := successful_operations + 1
            ELSE
                current_operations(device) := FAILED;
                failed_operations := failed_operations + 1
            END;
            operation_timers(device) := 0
        END;
    
    -- Обновление таймеров
    UpdateTimers = 
        PRE TRUE
        THEN
            -- Обновление таймеров устройств
            device_timers := {device | device : DEVICE_TYPE & device : dom(device_timers) & device_timers(device) > 0} * 
                           {device | device : DEVICE_TYPE & device : dom(device_timers) & device_timers(device) - 1};
            
            -- Обновление таймеров операций
            operation_timers := {device | device : DEVICE_TYPE & device : dom(operation_timers) & operation_timers(device) > 0} * 
                              {device | device : DEVICE_TYPE & device : dom(operation_timers) & operation_timers(device) - 1}
        END;
    
    -- Проверка безопасности
    CheckSafety = 
        PRE TRUE
        THEN
            -- Проверка аварийных порогов
            IF sensor_signals(HIGH_TEMP) > alarm_thresholds(HIGH_TEMP) THEN
                ActivateAlarm(HIGH_TEMP, CRITICAL)
            END;
            
            IF sensor_signals(LOW_TEMP) < alarm_thresholds(LOW_TEMP) THEN
                ActivateAlarm(LOW_TEMP, HIGH)
            END;
            
            IF sensor_signals(HIGH_PRESSURE) > alarm_thresholds(HIGH_PRESSURE) THEN
                ActivateAlarm(HIGH_PRESSURE, CRITICAL)
            END;
            
            IF sensor_signals(LOW_PRESSURE) < alarm_thresholds(LOW_PRESSURE) THEN
                ActivateAlarm(LOW_PRESSURE, HIGH)
            END
        END;
    
    -- Вход пользователя в систему
    LoginUser(user_type) = 
        PRE user_type : USER_TYPE
        THEN
            active_users(user_type) := TRUE
        END;
    
    -- Выход пользователя из системы
    LogoutUser(user_type) = 
        PRE user_type : USER_TYPE & 
             user_type : dom(active_users)
        THEN
            active_users(user_type) := FALSE
        END;
    
    -- Настройка устройства
    ConfigureDevice(device, config_value) = 
        PRE device : DEVICE_TYPE & 
             config_value : NATURAL &
             device : dom(devices)
        THEN
            device_configs(device) := config_value
        END;
    
    -- Установка лимитов операций
    SetOperationLimits(device, limit) = 
        PRE device : DEVICE_TYPE & 
             limit : NATURAL &
             device : dom(devices)
        THEN
            operation_limits(device) := limit
        END;
    
    -- Включение/выключение блокировки безопасности
    SetSafetyInterlock(device, enabled) = 
        PRE device : DEVICE_TYPE & 
             enabled : BOOL &
             device : dom(devices)
        THEN
            safety_interlocks(device) := enabled
        END;
    
    -- Плановое обслуживание
    ScheduleMaintenance(device) = 
        PRE device : DEVICE_TYPE & 
             device : dom(devices) &
             devices(device) = OFF
        THEN
            devices(device) := MAINTENANCE;
            maintenance_count := maintenance_count + 1
        END;
    
    -- Завершение обслуживания
    CompleteMaintenance(device) = 
        PRE device : DEVICE_TYPE & 
             device : dom(devices) &
             devices(device) = MAINTENANCE
        THEN
            devices(device) := OFF
        END

END
