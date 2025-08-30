MACHINE TrafficLight
-- ProB модель светофора на языке B
-- B методология основана на теории множеств и логике первого порядка
-- Демонстрирует формальные методы и математическую строгость

SETS
    LIGHT_STATE = {red, yellow, green};
    TIMER_STATE = {idle, counting, timeout}

VARIABLES
    light_state,
    cars_waiting,
    pedestrian_waiting,
    timer_state,
    timer_count,
    timer_limit

INVARIANT
    light_state : LIGHT_STATE &
    cars_waiting : NAT &
    cars_waiting <= 10 &
    pedestrian_waiting : BOOL &
    timer_state : TIMER_STATE &
    timer_count : NAT &
    timer_limit : NAT &
    timer_count <= timer_limit &
    (timer_state = idle => timer_count = 0 & timer_limit = 0) &
    (timer_state = counting => timer_count < timer_limit) &
    (timer_state = timeout => timer_count >= timer_limit)

INITIALISATION
    light_state := red ||
    cars_waiting := 0 ||
    pedestrian_waiting := FALSE ||
    timer_state := idle ||
    timer_count := 0 ||
    timer_limit := 0

OPERATIONS
    -- Запуск таймера
    start_timer(limit) =
        PRE limit : NAT & limit > 0
        THEN
            timer_state := counting ||
            timer_count := 0 ||
            timer_limit := limit
        END;
    
    -- Увеличение счетчика таймера
    tick =
        PRE timer_state = counting
        THEN
            timer_count := timer_count + 1 ||
            IF timer_count + 1 >= timer_limit THEN
                timer_state := timeout
            ELSE
                timer_state := counting
            END
        END;
    
    -- Сброс таймера
    reset_timer =
        PRE timer_state = counting | timer_state = timeout
        THEN
            timer_state := idle ||
            timer_count := 0 ||
            timer_limit := 0
        END;
    
    -- Переход на желтый свет
    to_yellow =
        PRE light_state = red & (cars_waiting > 0 | pedestrian_waiting)
        THEN
            light_state := yellow ||
            start_timer(3)
        END;
    
    -- Переход на зеленый свет
    to_green =
        PRE light_state = yellow & timer_state = timeout
        THEN
            light_state := green ||
            start_timer(8)
        END;
    
    -- Переход на красный свет
    to_red =
        PRE light_state = green & timer_state = timeout
        THEN
            light_state := red ||
            reset_timer ||
            IF cars_waiting > 0 THEN
                cars_waiting := cars_waiting - 1
            END ||
            pedestrian_waiting := FALSE
        END;
    
    -- Прибытие машины
    car_arrive =
        PRE cars_waiting < 10
        THEN
            cars_waiting := cars_waiting + 1
        END;
    
    -- Прибытие пешехода
    pedestrian_arrive =
        PRE NOT pedestrian_waiting
        THEN
            pedestrian_waiting := TRUE
        END

END


