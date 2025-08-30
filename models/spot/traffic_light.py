#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Spot библиотека для работы с автоматами Бюхи
Демонстрирует работу с LTL формулами и автоматами
Spot - это библиотека для работы с ω-автоматами и временной логикой
"""

import spot
from spot import automaton
from spot import formula

def demonstrate_spot_basics():
    """
    Демонстрация базовых возможностей Spot
    """
    print("=== Демонстрация библиотеки Spot ===\n")
    
    # 1. Создание LTL формул
    print("1. Создание LTL формул:")
    
    # Формула безопасности: никогда не должно быть зеленого света при ожидающем пешеходе
    safety_formula = formula("G(!(pedestrian_waiting & green_light))")
    print(f"   Формула безопасности: {safety_formula}")
    
    # Формула живости: если пешеход ждет, то в конце концов получит зеленый свет
    liveness_formula = formula("G(pedestrian_waiting -> F green_light)")
    print(f"   Формула живости: {liveness_formula}")
    
    # Формула справедливости: светофор не может "зависнуть" в одном состоянии
    fairness_formula = formula("G(red_light -> F yellow_light) & G(yellow_light -> F green_light)")
    print(f"   Формула справедливости: {fairness_formula}")
    
    print()
    
    # 2. Преобразование LTL в автомат Бюхи
    print("2. Преобразование LTL в автомат Бюхи:")
    
    # Создание автомата для формулы безопасности
    safety_automaton = safety_formula.translate()
    print(f"   Автомат для формулы безопасности:")
    print(f"   - Количество состояний: {safety_automaton.num_states()}")
    print(f"   - Количество переходов: {safety_automaton.num_edges()}")
    print(f"   - Начальные состояния: {safety_automaton.get_init_state_number()}")
    
    # Создание автомата для формулы живости
    liveness_automaton = liveness_formula.translate()
    print(f"   Автомат для формулы животи:")
    print(f"   - Количество состояний: {liveness_automaton.num_states()}")
    print(f"   - Количество переходов: {liveness_automaton.num_edges()}")
    
    print()
    
    # 3. Операции с автоматами
    print("3. Операции с автоматами:")
    
    # Объединение автоматов (логическое ИЛИ)
    combined_automaton = safety_automaton | liveness_automaton
    print(f"   Объединение автоматов (ИЛИ):")
    print(f"   - Количество состояний: {combined_automaton.num_states()}")
    
    # Пересечение автоматов (логическое И)
    intersection_automaton = safety_automaton & liveness_automaton
    print(f"   Пересечение автоматов (И):")
    print(f"   - Количество состояний: {intersection_automaton.num_states()}")
    
    print()
    
    # 4. Минимизация автоматов
    print("4. Минимизация автоматов:")
    
    # Минимизация автомата безопасности
    minimized_safety = safety_automaton.postprocess('BA', 'small')
    print(f"   Минимизированный автомат безопасности:")
    print(f"   - Исходное количество состояний: {safety_automaton.num_states()}")
    print(f"   - Минимизированное количество состояний: {minimized_safety.num_states()}")
    
    print()
    
    # 5. Проверка эквивалентности формул
    print("5. Проверка эквивалентности формул:")
    
    # Создание эквивалентных формул
    formula1 = formula("G(!(a & b))")
    formula2 = formula("G(!a | !b)")
    
    # Проверка эквивалентности
    are_equivalent = formula1.equivalent_to(formula2)
    print(f"   Формулы 'G(!(a & b))' и 'G(!a | !b)' эквивалентны: {are_equivalent}")
    
    print()
    
    # 6. Работа с ω-словами
    print("6. Работа с ω-словами:")
    
    # Создание бесконечного слова
    word = spot.word("a", "b", "c")
    print(f"   Создано ω-слово: {word}")
    
    # Проверка принятия слова автоматом
    is_accepted = safety_automaton.accepts(word)
    print(f"   Автомат безопасности принимает слово: {is_accepted}")
    
    print()

def demonstrate_traffic_light_system():
    """
    Демонстрация моделирования системы светофора с помощью Spot
    """
    print("=== Моделирование системы светофора ===\n")
    
    # Определение атомарных высказываний
    atoms = {
        'red_light': 'Красный свет горит',
        'yellow_light': 'Желтый свет горит', 
        'green_light': 'Зеленый свет горит',
        'pedestrian_waiting': 'Пешеход ждет',
        'car_waiting': 'Машина ждет'
    }
    
    print("Атомарные высказывания:")
    for atom, description in atoms.items():
        print(f"   {atom}: {description}")
    
    print()
    
    # Создание LTL спецификаций для светофора
    print("LTL спецификации для светофора:")
    
    # 1. Безопасность: только один свет может гореть одновременно
    safety_mutual_exclusion = formula("G(!(red_light & yellow_light) & !(yellow_light & green_light) & !(red_light & green_light))")
    print(f"   1. Взаимоисключение: {safety_mutual_exclusion}")
    
    # 2. Безопасность: не должно быть зеленого света при ожидающем пешеходе
    safety_pedestrian = formula("G(!(pedestrian_waiting & green_light))")
    print(f"   2. Безопасность пешехода: {safety_pedestrian}")
    
    # 3. Живость: если пешеход ждет, то в конце концов получит зеленый свет
    liveness_pedestrian = formula("G(pedestrian_waiting -> F green_light)")
    print(f"   3. Живость пешехода: {liveness_pedestrian}")
    
    # 4. Справедливость: светофор не может "зависнуть" в одном состоянии
    fairness_red = formula("G(red_light -> F yellow_light)")
    fairness_yellow = formula("G(yellow_light -> F green_light)")
    fairness_green = formula("G(green_light -> F red_light)")
    print(f"   4. Справедливость переходов:")
    print(f"      - Красный -> Желтый: {fairness_red}")
    print(f"      - Желтый -> Зеленый: {fairness_yellow}")
    print(f"      - Зеленый -> Красный: {fairness_green}")
    
    print()
    
    # Создание автоматов для каждой спецификации
    print("Создание автоматов Бюхи:")
    
    automata = {
        'Взаимоисключение': safety_mutual_exclusion.translate(),
        'Безопасность пешехода': safety_pedestrian.translate(),
        'Живость пешехода': liveness_pedestrian.translate(),
        'Справедливость красный': fairness_red.translate(),
        'Справедливость желтый': fairness_yellow.translate(),
        'Справедливость зеленый': fairness_green.translate()
    }
    
    for name, aut in automata.items():
        print(f"   {name}: {aut.num_states()} состояний, {aut.num_edges()} переходов")
    
    print()
    
    # Композиция всех спецификаций
    print("Композиция всех спецификаций:")
    
    # Объединение всех формул безопасности (логическое И)
    all_safety = safety_mutual_exclusion & safety_pedestrian
    all_fairness = fairness_red & fairness_yellow & fairness_green
    all_specs = all_safety & liveness_pedestrian & all_fairness
    
    print(f"   Объединенная формула: {all_specs}")
    
    # Создание автомата для всей системы
    system_automaton = all_specs.translate()
    print(f"   Автомат системы: {system_automaton.num_states()} состояний, {system_automaton.num_edges()} переходов")
    
    # Минимизация
    minimized_system = system_automaton.postprocess('BA', 'small')
    print(f"   Минимизированный автомат: {minimized_system.num_states()} состояний, {minimized_system.num_edges()} переходов")
    
    print()

def demonstrate_advanced_features():
    """
    Демонстрация продвинутых возможностей Spot
    """
    print("=== Продвинутые возможности Spot ===\n")
    
    # 1. Работа с различными типами автоматов
    print("1. Типы автоматов:")
    
    # Создание формулы
    test_formula = formula("G(a -> F b)")
    
    # Различные типы автоматов
    tgba = test_formula.translate('TGBA')  # Transition-based Generalized Büchi Automaton
    ba = test_formula.translate('BA')      # Büchi Automaton
    monitor = test_formula.translate('Monitor')  # Monitor (без принятия)
    
    print(f"   TGBA: {tgba.num_states()} состояний, {tgba.num_edges()} переходов")
    print(f"   BA: {ba.num_states()} состояний, {ba.num_edges()} переходов")
    print(f"   Monitor: {monitor.num_states()} состояний, {monitor.num_edges()} переходов")
    
    print()
    
    # 2. Оптимизация автоматов
    print("2. Оптимизация автоматов:")
    
    # Различные стратегии оптимизации
    strategies = ['small', 'deterministic', 'complete']
    
    for strategy in strategies:
        optimized = test_formula.translate('BA', strategy)
        print(f"   Стратегия '{strategy}': {optimized.num_states()} состояний")
    
    print()
    
    # 3. Проверка свойств формул
    print("3. Проверка свойств формул:")
    
    # Проверка различных свойств
    test_formulas = [
        formula("true"),
        formula("false"),
        formula("a"),
        formula("G a"),
        formula("F a"),
        formula("a U b")
    ]
    
    for f in test_formulas:
        print(f"   Формула '{f}':")
        print(f"     - Тривиальна: {f.is_tt()}")
        print(f"     - Противоречива: {f.is_ff()}")
        print(f"     - Атомарная: {f.is_atomic_prop()}")
        print(f"     - Всегда истинна: {f.is_ltl_formula() and f.is_syntactic_persistence()}")
    
    print()

if __name__ == "__main__":
    try:
        # Проверка доступности Spot
        print("Spot версия:", spot.version())
        print("=" * 60)
        
        # Демонстрация возможностей
        demonstrate_spot_basics()
        demonstrate_traffic_light_system()
        demonstrate_advanced_features()
        
        print("=" * 60)
        print("Демонстрация завершена успешно!")
        
    except ImportError:
        print("Ошибка: библиотека Spot не установлена.")
        print("Установите Spot: pip install spot")
    except Exception as e:
        print(f"Ошибка при выполнении: {e}")
