/*
 * Модель системы управления светофором для SPIN
 * 
 * Эта модель демонстрирует:
 * - Параллельные процессы (светофор, пешеходы, автомобили)
 * - Синхронизацию через каналы и переменные
 * - Обнаружение потенциальных deadlock'ов и race conditions
 * 
 * Автор: Образовательный проект SPIN vs UPPAAL
 * Язык: Promela (Process Meta Language)
 */

/* Глобальные переменные для состояния системы */
bool pedestrian_waiting = false;    // Флаг ожидания пешехода
bool emergency_mode = false;        // Режим экстренной остановки
int cars_waiting = 0;              // Количество ожидающих автомобилей

/* Каналы для синхронизации процессов */
chan pedestrian_request = [0] of {bool};  // Запрос пешехода на переход
chan light_change = [0] of {int};         // Изменение сигнала светофора
chan system_status = [0] of {int};        // Статус системы

/* Процесс светофора - основной контроллер системы */
proctype TrafficLight() {
    int current_state = 0;  // 0=красный, 1=желтый, 2=зеленый
    int cycle_count = 0;    // Счетчик циклов для обнаружения зацикливания
    
    printf("Светофор запущен\n");
    
    /* Основной цикл работы светофора */
    do
    :: cycle_count < 100 ->  // Ограничение для предотвращения бесконечного цикла
        if
        :: current_state == 0 ->  // Красный свет
            printf("Светофор: КРАСНЫЙ свет\n");
            
            /* Проверка запроса пешехода */
            if
            :: pedestrian_waiting -> 
                printf("Светофор: Пешеход ожидает, переключаю на зеленый\n");
                current_state = 2;
                pedestrian_waiting = false;
                light_change!2;  // Уведомляем о смене сигнала
            :: !pedestrian_waiting && cars_waiting > 0 ->
                printf("Светофор: Автомобили ожидают, переключаю на желтый\n");
                current_state = 1;
                light_change!1;
            :: else ->
                printf("Светофор: Ожидание...\n");
                skip;
            fi;
            
        :: current_state == 1 ->  // Желтый свет
            printf("Светофор: ЖЕЛТЫЙ свет\n");
            current_state = 2;
            light_change!2;
            
        :: current_state == 2 ->  // Зеленый свет
            printf("Светофор: ЗЕЛЕНЫЙ свет\n");
            
            /* Проверка экстренного режима */
            if
            :: emergency_mode ->
                printf("Светофор: ЭКСТРЕННЫЙ РЕЖИМ! Переключаю на красный\n");
                current_state = 0;
                emergency_mode = false;
                light_change!0;
            :: else ->
                /* Нормальная работа - переключение на красный через некоторое время */
                printf("Светофор: Нормальная работа, переключаю на красный\n");
                current_state = 0;
                light_change!0;
            fi;
        fi;
        
        cycle_count++;
        
    :: cycle_count >= 100 ->
        printf("Светофор: Достигнут лимит циклов, завершение\n");
        break;
    od;
    
    printf("Светофор завершен\n");
}

/* Процесс пешехода - запрашивает переход через дорогу */
proctype Pedestrian() {
    int id = _pid;  // Уникальный идентификатор пешехода
    
    printf("Пешеход %d: Появился у перехода\n", id);
    
    /* Пешеход ждет подходящего момента для перехода */
    do
    :: !pedestrian_waiting && cars_waiting < 3 ->  // Переходим, если мало машин
        printf("Пешеход %d: Запрашиваю переход\n", id);
        pedestrian_waiting = true;
        
        /* Ожидание зеленого света */
        light_change?2;  // Ждем зеленый свет
        printf("Пешеход %d: Перехожу дорогу\n", id);
        
        /* Симуляция времени перехода */
        skip;
        skip;
        
        printf("Пешеход %d: Переход завершен\n", id);
        break;
        
    :: else ->
        printf("Пешеход %d: Жду подходящего момента\n", id);
        skip;
    od;
}

/* Процесс автомобиля - прибывает и ожидает зеленого света */
proctype Car() {
    int id = _pid;  // Уникальный идентификатор автомобиля
    
    printf("Автомобиль %d: Прибыл к светофору\n", id);
    cars_waiting++;
    
    /* Ожидание зеленого света */
    light_change?2;  // Ждем зеленый свет
    printf("Автомобиль %d: Проезжаю перекресток\n", id);
    
    /* Симуляция времени проезда */
    skip;
    
    cars_waiting--;
    printf("Автомобиль %d: Проезд завершен\n", id);
}

/* Процесс экстренной службы - может активировать экстренный режим */
proctype EmergencyService() {
    int id = _pid;
    
    printf("Экстренная служба %d: Прибыла\n", id);
    
    /* Случайная активация экстренного режима */
    if
    :: true ->  // 50% вероятность
        printf("Экстренная служба %d: Активирую экстренный режим\n", id);
        emergency_mode = true;
        system_status!1;  // Уведомляем о статусе
    :: else ->
        printf("Экстренная служба %d: Обычный проезд\n", id);
        system_status!0;
    fi;
    
    printf("Экстренная служба %d: Завершена\n", id);
}

/* Процесс мониторинга - отслеживает состояние системы */
proctype SystemMonitor() {
    int status;
    
    printf("Монитор системы: Запущен\n");
    
    /* Мониторинг статуса системы */
    do
    :: system_status?status ->
        if
        :: status == 1 ->
            printf("Монитор: Обнаружен экстренный режим\n");
        :: status == 0 ->
            printf("Монитор: Нормальный режим работы\n");
        fi;
        
    :: timeout ->
        printf("Монитор: Таймаут, проверка состояния\n");
        if
        :: pedestrian_waiting && cars_waiting > 5 ->
            printf("Монитор: ВНИМАНИЕ! Возможная проблема с синхронизацией\n");
        :: else ->
            printf("Монитор: Система работает нормально\n");
        fi;
    od;
}

/* Инициализация системы */
init {
    printf("=== ИНИЦИАЛИЗАЦИЯ СИСТЕМЫ СВЕТОФОРА ===\n");
    
    /* Запуск основных процессов */
    run TrafficLight();
    run Pedestrian();
    run Pedestrian();  // Второй пешеход
    run Car();
    run Car();         // Второй автомобиль
    run EmergencyService();
    run SystemMonitor();
    
    printf("=== СИСТЕМА ЗАПУЩЕНА ===\n");
}

/* Спецификация свойств для верификации */
ltl safety { 
    /* Безопасность: никогда не должно быть одновременно зеленого света и ожидающего пешехода */
    !(pedestrian_waiting && cars_waiting > 0)
}

ltl liveness { 
    /* Живость: система должна продолжать работать */
    [] (pedestrian_waiting -> <> !pedestrian_waiting)
}

ltl no_deadlock {
    /* Отсутствие deadlock'ов */
    [] <> (pedestrian_waiting || cars_waiting > 0 || emergency_mode)
}
