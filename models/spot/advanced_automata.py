#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Spot модель продвинутых автоматов
Автор: Senior Developer
Описание: Модель системы с несколькими автоматами, синхронизацией и сложной логикой
"""

import spot
from spot import automaton
import sys

def create_basic_automaton():
    """Создание базового автомата для системы управления"""
    
    # Создание автомата
    aut = spot.make_twa_graph()
    
    # Определение состояний
    states = {
        'INIT': 0,
        'READY': 1,
        'ACTIVE': 2,
        'ERROR': 3,
        'RECOVERING': 4,
        'MAINTENANCE': 5
    }
    
    # Добавление состояний
    for state_name, state_id in states.items():
        aut.new_state()
        if state_id == 0:  # INIT - начальное состояние
            aut.set_init_state(state_id)
    
    # Определение атомарных предложений
    ap_names = ['start', 'stop', 'error', 'recover', 'maintenance', 'ready']
    aut.register_ap_names(ap_names)
    
    # Добавление переходов
    # INIT -> READY (при получении сигнала ready)
    aut.new_edge(0, 1, spot.formula.And(spot.formula.ap('ready'), 
                                        spot.formula.Not(spot.formula.ap('error'))))
    
    # READY -> ACTIVE (при получении сигнала start)
    aut.new_edge(1, 2, spot.formula.And(spot.formula.ap('start'), 
                                        spot.formula.Not(spot.formula.ap('error'))))
    
    # ACTIVE -> READY (при получении сигнала stop)
    aut.new_edge(2, 1, spot.formula.ap('stop'))
    
    # Любое состояние -> ERROR (при получении сигнала error)
    for state_id in [0, 1, 2, 4, 5]:
        aut.new_edge(state_id, 3, spot.formula.ap('error'))
    
    # ERROR -> RECOVERING (при получении сигнала recover)
    aut.new_edge(3, 4, spot.formula.ap('recover'))
    
    # RECOVERING -> READY (при успешном восстановлении)
    aut.new_edge(4, 1, spot.formula.And(spot.formula.ap('ready'), 
                                        spot.formula.Not(spot.formula.ap('error'))))
    
    # Любое состояние -> MAINTENANCE (при получении сигнала maintenance)
    for state_id in [0, 1, 2, 4]:
        aut.new_edge(state_id, 5, spot.formula.ap('maintenance'))
    
    # MAINTENANCE -> READY (при завершении обслуживания)
    aut.new_edge(5, 1, spot.formula.And(spot.formula.ap('ready'), 
                                        spot.formula.Not(spot.formula.ap('error'))))
    
    # Самоциклы для стабильных состояний
    aut.new_edge(1, 1, spot.formula.And(spot.formula.Not(spot.formula.ap('start')), 
                                        spot.formula.Not(spot.formula.ap('error')),
                                        spot.formula.Not(spot.formula.ap('maintenance')))
    aut.new_edge(2, 2, spot.formula.And(spot.formula.Not(spot.formula.ap('stop')), 
                                        spot.formula.Not(spot.formula.ap('error')),
                                        spot.formula.Not(spot.formula.ap('maintenance')))
    
    return aut

def create_pump_automaton():
    """Создание автомата для управления насосом"""
    
    aut = spot.make_twa_graph()
    
    # Состояния насоса
    states = {
        'STOPPED': 0,
        'STARTING': 1,
        'RUNNING': 2,
        'STOPPING': 3,
        'ERROR': 4,
        'MAINTENANCE': 5
    }
    
    # Добавление состояний
    for state_name, state_id in states.items():
        aut.new_state()
        if state_id == 0:
            aut.set_init_state(state_id)
    
    # Атомарные предложения
    ap_names = ['start_cmd', 'stop_cmd', 'pump_ready', 'pump_fail', 
                'maintenance_req', 'maintenance_done', 'emergency']
    aut.register_ap_names(ap_names)
    
    # Переходы
    # STOPPED -> STARTING
    aut.new_edge(0, 1, spot.formula.And(spot.formula.ap('start_cmd'), 
                                        spot.formula.ap('pump_ready'),
                                        spot.formula.Not(spot.formula.ap('emergency'))))
    
    # STARTING -> RUNNING
    aut.new_edge(1, 2, spot.formula.ap('pump_ready'))
    
    # RUNNING -> STOPPING
    aut.new_edge(2, 3, spot.formula.Or(spot.formula.ap('stop_cmd'), 
                                       spot.formula.ap('emergency')))
    
    # STOPPING -> STOPPED
    aut.new_edge(3, 0, spot.formula.Not(spot.formula.ap('pump_ready')))
    
    # Любое состояние -> ERROR
    for state_id in [0, 1, 2, 3, 5]:
        aut.new_edge(state_id, 4, spot.formula.ap('pump_fail'))
    
    # ERROR -> STOPPED (при восстановлении)
    aut.new_edge(4, 0, spot.formula.And(spot.formula.Not(spot.formula.ap('pump_fail')), 
                                        spot.formula.ap('pump_ready')))
    
    # Любое состояние -> MAINTENANCE
    for state_id in [0, 1, 2, 4]:
        aut.new_edge(state_id, 5, spot.formula.ap('maintenance_req'))
    
    # MAINTENANCE -> STOPPED
    aut.new_edge(5, 0, spot.formula.ap('maintenance_done'))
    
    return aut

def create_valve_automaton():
    """Создание автомата для управления клапаном"""
    
    aut = spot.make_twa_graph()
    
    # Состояния клапана
    states = {
        'CLOSED': 0,
        'OPENING': 1,
        'OPEN': 2,
        'CLOSING': 3,
        'ERROR': 4,
        'MAINTENANCE': 5
    }
    
    # Добавление состояний
    for state_name, state_id in states.items():
        aut.new_state()
        if state_id == 0:
            aut.set_init_state(state_id)
    
    # Атомарные предложения
    ap_names = ['open_cmd', 'close_cmd', 'valve_ready', 'valve_fail',
                'maintenance_req', 'maintenance_done', 'emergency']
    aut.register_ap_names(ap_names)
    
    # Переходы
    # CLOSED -> OPENING
    aut.new_edge(0, 1, spot.formula.And(spot.formula.ap('open_cmd'), 
                                        spot.formula.ap('valve_ready'),
                                        spot.formula.Not(spot.formula.ap('emergency'))))
    
    # OPENING -> OPEN
    aut.new_edge(1, 2, spot.formula.ap('valve_ready'))
    
    # OPEN -> CLOSING
    aut.new_edge(2, 3, spot.formula.Or(spot.formula.ap('close_cmd'), 
                                       spot.formula.ap('emergency')))
    
    # CLOSING -> CLOSED
    aut.new_edge(3, 0, spot.formula.Not(spot.formula.ap('valve_ready')))
    
    # Любое состояние -> ERROR
    for state_id in [0, 1, 2, 3, 5]:
        aut.new_edge(state_id, 4, spot.formula.ap('valve_fail'))
    
    # ERROR -> CLOSED (при восстановлении)
    aut.new_edge(4, 0, spot.formula.And(spot.formula.Not(spot.formula.ap('valve_fail')), 
                                        spot.formula.ap('valve_ready')))
    
    # Любое состояние -> MAINTENANCE
    for state_id in [0, 1, 2, 4]:
        aut.new_edge(state_id, 5, spot.formula.ap('maintenance_req'))
    
    # MAINTENANCE -> CLOSED
    aut.new_edge(5, 0, spot.formula.ap('maintenance_done'))
    
    return aut

def create_safety_automaton():
    """Создание автомата для системы безопасности"""
    
    aut = spot.make_twa_graph()
    
    # Состояния безопасности
    states = {
        'SAFE': 0,
        'WARNING': 1,
        'ALARM': 2,
        'EMERGENCY': 3,
        'LOCKDOWN': 4
    }
    
    # Добавление состояний
    for state_name, state_id in states.items():
        aut.new_state()
        if state_id == 0:
            aut.set_init_state(state_id)
    
    # Атомарные предложения
    ap_names = ['sensor_warning', 'sensor_alarm', 'emergency_trigger', 
                'acknowledge', 'reset', 'clear_emergency']
    aut.register_ap_names(ap_names)
    
    # Переходы
    # SAFE -> WARNING
    aut.new_edge(0, 1, spot.formula.ap('sensor_warning'))
    
    # WARNING -> SAFE
    aut.new_edge(1, 0, spot.formula.ap('reset'))
    
    # WARNING -> ALARM
    aut.new_edge(1, 2, spot.formula.ap('sensor_alarm'))
    
    # ALARM -> WARNING
    aut.new_edge(2, 1, spot.formula.ap('acknowledge'))
    
    # ALARM -> EMERGENCY
    aut.new_edge(2, 3, spot.formula.ap('emergency_trigger'))
    
    # EMERGENCY -> LOCKDOWN
    aut.new_edge(3, 4, spot.formula.And(spot.formula.ap('emergency_trigger'), 
                                        spot.formula.Not(spot.formula.ap('acknowledge'))))
    
    # LOCKDOWN -> EMERGENCY
    aut.new_edge(4, 3, spot.formula.ap('acknowledge'))
    
    # EMERGENCY -> ALARM
    aut.new_edge(3, 2, spot.formula.ap('acknowledge'))
    
    # ALARM -> SAFE
    aut.new_edge(2, 0, spot.formula.ap('reset'))
    
    # Самоциклы
    aut.new_edge(0, 0, spot.formula.And(spot.formula.Not(spot.formula.ap('sensor_warning')), 
                                        spot.formula.Not(spot.formula.ap('sensor_alarm'))))
    aut.new_edge(1, 1, spot.formula.And(spot.formula.Not(spot.formula.ap('reset')), 
                                        spot.formula.Not(spot.formula.ap('sensor_alarm'))))
    aut.new_edge(2, 2, spot.formula.And(spot.formula.Not(spot.formula.ap('acknowledge')), 
                                        spot.formula.Not(spot.formula.ap('emergency_trigger'))))
    
    return aut

def create_system_automaton():
    """Создание главного автомата системы"""
    
    aut = spot.make_twa_graph()
    
    # Состояния системы
    states = {
        'INITIALIZING': 0,
        'OPERATIONAL': 1,
        'DEGRADED': 2,
        'EMERGENCY': 3,
        'SHUTDOWN': 4,
        'MAINTENANCE': 5
    }
    
    # Добавление состояний
    for state_name, state_id in states.items():
        aut.new_state()
        if state_id == 0:
            aut.set_init_state(state_id)
    
    # Атомарные предложения
    ap_names = ['system_ready', 'component_fail', 'emergency_stop', 
                'maintenance_mode', 'shutdown_cmd', 'recovery_complete']
    aut.register_ap_names(ap_names)
    
    # Переходы
    # INITIALIZING -> OPERATIONAL
    aut.new_edge(0, 1, spot.formula.And(spot.formula.ap('system_ready'), 
                                        spot.formula.Not(spot.formula.ap('component_fail'))))
    
    # OPERATIONAL -> DEGRADED
    aut.new_edge(1, 2, spot.formula.And(spot.formula.ap('component_fail'), 
                                        spot.formula.Not(spot.formula.ap('emergency_stop'))))
    
    # DEGRADED -> OPERATIONAL
    aut.new_edge(2, 1, spot.formula.ap('recovery_complete'))
    
    # DEGRADED -> EMERGENCY
    aut.new_edge(2, 3, spot.formula.ap('emergency_stop'))
    
    # OPERATIONAL -> EMERGENCY
    aut.new_edge(1, 3, spot.formula.ap('emergency_stop'))
    
    # EMERGENCY -> SHUTDOWN
    aut.new_edge(3, 4, spot.formula.ap('shutdown_cmd'))
    
    # EMERGENCY -> MAINTENANCE
    aut.new_edge(3, 5, spot.formula.ap('maintenance_mode'))
    
    # MAINTENANCE -> OPERATIONAL
    aut.new_edge(5, 1, spot.formula.And(spot.formula.ap('system_ready'), 
                                        spot.formula.Not(spot.formula.ap('component_fail'))))
    
    # SHUTDOWN -> INITIALIZING (при перезапуске)
    aut.new_edge(4, 0, spot.formula.ap('system_ready'))
    
    return aut

def create_composite_automaton():
    """Создание составного автомата из нескольких компонентов"""
    
    # Создание отдельных автоматов
    basic_aut = create_basic_automaton()
    pump_aut = create_pump_automaton()
    valve_aut = create_valve_automaton()
    safety_aut = create_safety_automaton()
    system_aut = create_system_automaton()
    
    # Объединение автоматов (простая композиция)
    # В реальности здесь была бы более сложная логика композиции
    
    print("Созданы следующие автоматы:")
    print(f"1. Базовый автомат: {basic_aut.num_states()} состояний")
    print(f"2. Автомат насоса: {pump_aut.num_states()} состояний")
    print(f"3. Автомат клапана: {valve_aut.num_states()} состояний")
    print(f"4. Автомат безопасности: {safety_aut.num_states()} состояний")
    print(f"5. Автомат системы: {system_aut.num_states()} состояний")
    
    return [basic_aut, pump_aut, valve_aut, safety_aut, system_aut]

def verify_automata_properties(automata):
    """Проверка свойств автоматов"""
    
    print("\nПроверка свойств автоматов:")
    
    for i, aut in enumerate(automata):
        print(f"\nАвтомат {i+1}:")
        
        # Проверка детерминированности
        is_det = aut.is_deterministic()
        print(f"  Детерминированный: {is_det}")
        
        # Проверка завершенности
        is_complete = aut.is_complete()
        print(f"  Завершенный: {is_complete}")
        
        # Проверка слабой справедливости
        is_weak = aut.is_weak()
        print(f"  Слабый: {is_weak}")
        
        # Проверка терминальности
        is_terminal = aut.is_terminal()
        print(f"  Терминальный: {is_terminal}")

def create_ltl_formulas():
    """Создание LTL формул для проверки"""
    
    formulas = []
    
    # Формула безопасности: система не должна находиться в состоянии ERROR
    safety_formula = spot.formula.Not(spot.formula.F(spot.formula.ap('error')))
    formulas.append(("Безопасность", safety_formula))
    
    # Формула живости: система должна достигать состояния READY
    liveness_formula = spot.formula.F(spot.formula.ap('ready'))
    formulas.append(("Живость", liveness_formula))
    
    # Формула восстановления: после ошибки система должна восстанавливаться
    recovery_formula = spot.formula.G(spot.formula.ap('error') >> 
                                     spot.formula.F(spot.formula.ap('ready')))
    formulas.append(("Восстановление", recovery_formula))
    
    # Формула взаимного исключения: насос и клапан не могут быть активны одновременно
    mutex_formula = spot.formula.G(spot.formula.Not(spot.formula.And(spot.formula.ap('pump_running'), 
                                                                   spot.formula.ap('valve_open'))))
    formulas.append(("Взаимное исключение", mutex_formula))
    
    # Формула приоритетов: аварийная остановка имеет приоритет над всеми операциями
    priority_formula = spot.formula.G(spot.formula.ap('emergency') >> 
                                     spot.formula.X(spot.formula.Not(spot.formula.ap('start_cmd'))))
    formulas.append(("Приоритеты", priority_formula))
    
    return formulas

def main():
    """Главная функция"""
    
    print("=== Spot модель продвинутых автоматов ===\n")
    
    try:
        # Создание составного автомата
        automata = create_composite_automaton()
        
        # Проверка свойств
        verify_automata_properties(automata)
        
        # Создание LTL формул
        formulas = create_ltl_formulas()
        
        print("\nСозданные LTL формулы:")
        for name, formula in formulas:
            print(f"  {name}: {formula}")
        
        # Сохранение автоматов в файлы
        for i, aut in enumerate(automata):
            filename = f"automaton_{i+1}.hoa"
            with open(filename, 'w') as f:
                f.write(aut.to_str('hoa'))
            print(f"\nАвтомат {i+1} сохранен в {filename}")
        
        print("\nМоделирование завершено успешно!")
        
    except Exception as e:
        print(f"Ошибка при создании автоматов: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()


