PROGRAM PumpControl
VAR
    pump1_status: INT := 0;  // 0=остановлен, 1=запущен, 2=ошибка
    pump2_status: INT := 0;
    system_mode: INT := 0;   // 0=ручной, 1=автоматический, 2=аварийный
    pressure_ok: BOOL := TRUE;
    level_ok: BOOL := TRUE;
    emergency_stop: BOOL := FALSE;
    start_button1: BOOL;
    start_button2: BOOL;
    stop_button1: BOOL;
    stop_button2: BOOL;
    emergency_button: BOOL;
    i: INT;
    array_values: ARRAY[1..10] OF INT;
END_VAR

// Основная логика управления
IF emergency_button OR NOT pressure_ok OR NOT level_ok THEN
    emergency_stop := TRUE;
    system_mode := 2;
    pump1_status := 0;
    pump2_status := 0;
END_IF;

// Запуск насоса 1
IF start_button1 AND NOT emergency_stop AND pressure_ok AND level_ok AND pump1_status = 0 THEN
    pump1_status := 1;
END_IF;

// Запуск насоса 2
IF start_button2 AND NOT emergency_stop AND pressure_ok AND level_ok AND pump2_status = 0 THEN
    pump2_status := 1;
END_IF;

// Остановка насосов
IF stop_button1 AND pump1_status = 1 THEN
    pump1_status := 0;
END_IF;

IF stop_button2 AND pump2_status = 1 THEN
    pump2_status := 0;
END_IF;

// Выбор режима работы
CASE system_mode OF
    0: // Ручной режим
        pump1_status := 0;
        pump2_status := 0;
    1: // Автоматический режим
        IF pressure_ok AND level_ok THEN
            pump1_status := 1;
        END_IF;
    ELSE // Аварийный режим
        emergency_stop := TRUE;
        pump1_status := 0;
        pump2_status := 0;
END_CASE;

// Обработка массива значений
FOR i := 1 TO 10 DO
    IF array_values[i] > 100 THEN
        array_values[i] := array_values[i] / 2;
    END_IF;
END_FOR;

END_PROGRAM
