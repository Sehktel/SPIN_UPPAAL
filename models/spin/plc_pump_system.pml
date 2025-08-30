/*
 * Модель SPIN для системы управления насосами ПЛК
 * Демонстрирует применение формальных методов в программировании ПЛК
 * 
 * Система: Два насоса, система безопасности, протоколы запуска/остановки
 */

// Глобальные переменные системы
int pump1_status = 0;        // 0=остановлен, 1=запущен, 2=ошибка
int pump2_status = 0;        // 0=остановлен, 1=запущен, 2=ошибка
int system_mode = 0;         // 0=ручной, 1=автоматический, 2=аварийный
int pressure_ok = 1;         // 1=норма, 0=критично
int level_ok = 1;            // 1=норма, 0=критично
int emergency_stop = 0;      // 0=норма, 1=нажата
int maintenance_mode = 0;    // 0=рабочий, 1=обслуживание

// Каналы для синхронизации
chan start_command = [0] of {int};      // Команда запуска насоса
chan stop_command = [0] of {int};       // Команда остановки насоса
chan status_update = [0] of {int, int}; // Обновление статуса (насос, статус)
chan emergency_signal = [0] of {int};   // Сигнал аварии
chan safety_check = [0] of {int};       // Результат проверки безопасности

// Процесс ПЛК - основной контроллер
proctype PLCController() {
    int command;
    int pump_id;
    int new_status;
    
    do
    :: emergency_stop == 1 -> 
        // Аварийная остановка - приоритет
        if
        :: pump1_status == 1 -> pump1_status = 0
        :: pump2_status == 1 -> pump2_status = 0
        :: else -> skip
        fi;
        system_mode = 2;  // Переход в аварийный режим
        printf("EMERGENCY STOP ACTIVATED\n")
        
    :: start_command?command ->
        // Обработка команды запуска
        if
        :: command == 1 && pump1_status == 0 && safety_check_ok() ->
            pump1_status = 1;
            printf("PUMP1 STARTED\n")
        :: command == 2 && pump2_status == 0 && safety_check_ok() ->
            pump2_status = 1;
            printf("PUMP2 STARTED\n")
        :: else ->
            printf("START COMMAND REJECTED\n")
        fi
        
    :: stop_command?command ->
        // Обработка команды остановки
        if
        :: command == 1 && pump1_status == 1 ->
            pump1_status = 0;
            printf("PUMP1 STOPPED\n")
        :: command == 2 && pump2_status == 1 ->
            pump2_status = 0;
            printf("PUMP2 STOPPED\n")
        :: else ->
            printf("STOP COMMAND REJECTED\n")
        fi
        
    :: status_update?pump_id, new_status ->
        // Обновление статуса насоса
        if
        :: pump_id == 1 -> pump1_status = new_status
        :: pump_id == 2 -> pump2_status = new_status
        fi
        
    :: emergency_signal?command ->
        // Обработка аварийного сигнала
        emergency_stop = 1;
        system_mode = 2;
        printf("EMERGENCY SIGNAL RECEIVED\n")
        
    :: timeout ->
        // Таймаут - проверка состояния системы
        if
        :: pressure_ok == 0 || level_ok == 0 ->
            emergency_stop = 1;
            system_mode = 2;
            printf("SAFETY VIOLATION DETECTED\n")
        :: else ->
            skip
        fi
    od
}

// Процесс насоса 1
proctype Pump1() {
    int status;
    
    do
    :: status == 0 ->  // Остановлен
        if
        :: start_command!1 -> 
            status = 1;
            status_update!1, 1;
            printf("PUMP1: Starting...\n")
        :: else -> skip
        fi
        
    :: status == 1 ->  // Работает
        if
        :: stop_command!1 -> 
            status = 0;
            status_update!1, 0;
            printf("PUMP1: Stopping...\n")
        :: emergency_stop == 1 -> 
            status = 0;
            status_update!1, 0;
            printf("PUMP1: Emergency stop\n")
        :: else -> skip
        fi
        
    :: status == 2 ->  // Ошибка
        if
        :: maintenance_mode == 1 -> 
            status = 0;
            status_update!1, 0;
            printf("PUMP1: Reset after maintenance\n")
        :: else -> skip
        fi
    od
}

// Процесс насоса 2
proctype Pump2() {
    int status;
    
    do
    :: status == 0 ->  // Остановлен
        if
        :: start_command!2 -> 
            status = 1;
            status_update!2, 1;
            printf("PUMP2: Starting...\n")
        :: else -> skip
        fi
        
    :: status == 1 ->  // Работает
        if
        :: stop_command!2 -> 
            status = 0;
            status_update!2, 0;
            printf("PUMP2: Stopping...\n")
        :: emergency_stop == 1 -> 
            status = 0;
            status_update!2, 0;
            printf("PUMP2: Emergency stop\n")
        :: else -> skip
        fi
        
    :: status == 2 ->  // Ошибка
        if
        :: maintenance_mode == 1 -> 
            status = 0;
            status_update!2, 0;
            printf("PUMP2: Reset after maintenance\n")
        :: else -> skip
        fi
    od
}

// Процесс системы безопасности
proctype SafetySystem() {
    do
    :: pressure_ok == 1 && level_ok == 1 ->
        // Нормальные условия
        if
        :: emergency_stop == 1 ->
            pressure_ok = 0;
            level_ok = 0;
            printf("SAFETY: Emergency conditions activated\n")
        :: else -> skip
        fi
        
    :: pressure_ok == 0 || level_ok == 0 ->
        // Критические условия
        if
        :: emergency_stop == 0 ->
            pressure_ok = 1;
            level_ok = 1;
            printf("SAFETY: Normal conditions restored\n")
        :: else -> skip
        fi
    od
}

// Процесс оператора
proctype Operator() {
    do
    :: start_command!1 ->  // Запуск насоса 1
        printf("OPERATOR: Start pump 1\n")
        
    :: start_command!2 ->  // Запуск насоса 2
        printf("OPERATOR: Start pump 2\n")
        
    :: stop_command!1 ->   // Остановка насоса 1
        printf("OPERATOR: Stop pump 1\n")
        
    :: stop_command!2 ->   // Остановка насоса 2
        printf("OPERATOR: Stop pump 2\n")
        
    :: emergency_signal!1 ->  // Аварийный сигнал
        printf("OPERATOR: Emergency signal\n")
        
    :: timeout ->
        // Симуляция действий оператора
        skip
    od
}

// Функция проверки безопасности
inline safety_check_ok() {
    return (pressure_ok == 1 && level_ok == 1 && emergency_stop == 0)
}

// Инициализация системы
init {
    // Запуск всех процессов
    run PLCController();
    run Pump1();
    run Pump2();
    run SafetySystem();
    run Operator();
    
    printf("PLC PUMP SYSTEM INITIALIZED\n")
}

// LTL свойства для верификации

// Безопасность: никогда не должны работать оба насоса одновременно
ltl safety_no_dual_pumps { 
    !(pump1_status == 1 && pump2_status == 1) 
}

// Безопасность: насосы не должны работать при аварийной остановке
ltl safety_emergency_stop { 
    [] (emergency_stop == 1 -> (pump1_status == 0 && pump2_status == 0))
}

// Безопасность: насосы не должны работать при критических условиях
ltl safety_critical_conditions { 
    [] ((pressure_ok == 0 || level_ok == 0) -> 
         (pump1_status == 0 && pump2_status == 0))
}

// Живость: при нормальных условиях насосы могут запускаться
ltl liveness_pump_start { 
    [] ((pressure_ok == 1 && level_ok == 1 && emergency_stop == 0) -> 
         (<> (pump1_status == 1 || pump2_status == 1)))
}

// Справедливость: система не может "зависнуть" в аварийном режиме
ltl fairness_emergency_recovery { 
    [] (system_mode == 2 -> <> system_mode == 0)
}

// Протокол: корректная последовательность запуска
ltl protocol_startup_sequence { 
    [] (start_command -> 
        (<> (pump1_status == 1 || pump2_status == 1 || 
             emergency_stop == 1 || pressure_ok == 0 || level_ok == 0)))
}
