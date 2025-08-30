#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Специализированная модель протокольных автоматов для Spot
Моделирует различные сетевые протоколы с использованием автоматов и LTL формул
"""

import spot
from spot import twa_graph, formula
import sys

class ProtocolAutomata:
    """Класс для создания и анализа протокольных автоматов"""
    
    def __init__(self):
        """Инициализация с базовыми настройками"""
        self.automata = {}
        self.formulas = {}
        self.protocols = {}
        
    def create_tcp_automaton(self):
        """Создание автомата для TCP протокола"""
        # Состояния TCP
        states = ['CLOSED', 'LISTEN', 'SYN_SENT', 'SYN_RECEIVED', 
                 'ESTABLISHED', 'FIN_WAIT_1', 'FIN_WAIT_2', 'CLOSE_WAIT',
                 'CLOSING', 'LAST_ACK', 'TIME_WAIT']
        
        # События TCP
        events = ['passive_open', 'active_open', 'send_syn', 'receive_syn',
                  'send_syn_ack', 'receive_syn_ack', 'send_ack', 'receive_ack',
                  'send_fin', 'receive_fin', 'timeout', 'close']
        
        # Создание автомата
        tcp = twa_graph()
        tcp.set_name("TCP_Protocol")
        
        # Добавление состояний
        for i, state in enumerate(states):
            tcp.new_state()
            tcp.set_state_name(i, state)
        
        # Добавление переходов
        # CLOSED -> LISTEN (passive_open)
        tcp.new_edge(0, 1, formula.ap("passive_open"))
        # CLOSED -> SYN_SENT (active_open)
        tcp.new_edge(0, 2, formula.ap("active_open"))
        # LISTEN -> SYN_RECEIVED (receive_syn)
        tcp.new_edge(1, 3, formula.ap("receive_syn"))
        # SYN_SENT -> ESTABLISHED (receive_syn_ack + send_ack)
        tcp.new_edge(2, 4, formula.And(formula.ap("receive_syn_ack"), formula.ap("send_ack")))
        # SYN_RECEIVED -> ESTABLISHED (receive_ack)
        tcp.new_edge(3, 4, formula.ap("receive_ack"))
        # ESTABLISHED -> FIN_WAIT_1 (send_fin)
        tcp.new_edge(4, 5, formula.ap("send_fin"))
        # FIN_WAIT_1 -> FIN_WAIT_2 (receive_ack)
        tcp.new_edge(5, 6, formula.ap("receive_ack"))
        # FIN_WAIT_2 -> TIME_WAIT (receive_fin + send_ack)
        tcp.new_edge(6, 10, formula.And(formula.ap("receive_fin"), formula.ap("send_ack")))
        # ESTABLISHED -> CLOSE_WAIT (receive_fin)
        tcp.new_edge(4, 7, formula.ap("receive_fin"))
        # CLOSE_WAIT -> LAST_ACK (send_fin)
        tcp.new_edge(7, 9, formula.ap("send_fin"))
        # LAST_ACK -> CLOSED (receive_ack)
        tcp.new_edge(9, 0, formula.ap("receive_ack"))
        # TIME_WAIT -> CLOSED (timeout)
        tcp.new_edge(10, 0, formula.ap("timeout"))
        
        # Установка начального состояния
        tcp.set_init_state(0)
        
        # Установка принимающих состояний (ESTABLISHED)
        tcp.set_acceptance(4, True)
        
        self.automata['TCP'] = tcp
        return tcp
    
    def create_udp_automaton(self):
        """Создание автомата для UDP протокола"""
        # Состояния UDP (проще чем TCP)
        states = ['IDLE', 'SENDING', 'RECEIVING', 'ERROR']
        
        # События UDP
        events = ['send_datagram', 'receive_datagram', 'timeout', 'error']
        
        # Создание автомата
        udp = twa_graph()
        udp.set_name("UDP_Protocol")
        
        # Добавление состояний
        for i, state in enumerate(states):
            udp.new_state()
            udp.set_state_name(i, state)
        
        # Добавление переходов
        # IDLE -> SENDING (send_datagram)
        udp.new_edge(0, 1, formula.ap("send_datagram"))
        # IDLE -> RECEIVING (receive_datagram)
        udp.new_state()
        udp.new_edge(0, 2, formula.ap("receive_datagram"))
        # SENDING -> IDLE (timeout или завершение)
        udp.new_edge(1, 0, formula.Or(formula.ap("timeout"), formula.ap("complete")))
        # RECEIVING -> IDLE (завершение приема)
        udp.new_edge(2, 0, formula.ap("complete"))
        # Любое состояние -> ERROR (error)
        for i in range(len(states) - 1):
            udp.new_edge(i, 3, formula.ap("error"))
        # ERROR -> IDLE (recovery)
        udp.new_edge(3, 0, formula.ap("recovery"))
        
        # Установка начального состояния
        udp.set_init_state(0)
        
        # Установка принимающих состояний (IDLE, SENDING, RECEIVING)
        for i in range(3):
            udp.set_acceptance(i, True)
        
        self.automata['UDP'] = udp
        return udp
    
    def create_http_automaton(self):
        """Создание автомата для HTTP протокола"""
        # Состояния HTTP
        states = ['IDLE', 'REQUEST_SENT', 'RESPONSE_RECEIVED', 'PROCESSING', 'COMPLETED', 'ERROR']
        
        # События HTTP
        events = ['send_request', 'receive_response', 'process_data', 'complete', 'timeout', 'error']
        
        # Создание автомата
        http = twa_graph()
        http.set_name("HTTP_Protocol")
        
        # Добавление состояний
        for i, state in enumerate(states):
            http.new_state()
            http.set_state_name(i, state)
        
        # Добавление переходов
        # IDLE -> REQUEST_SENT (send_request)
        http.new_edge(0, 1, formula.ap("send_request"))
        # REQUEST_SENT -> RESPONSE_RECEIVED (receive_response)
        http.new_edge(1, 2, formula.ap("receive_response"))
        # RESPONSE_RECEIVED -> PROCESSING (process_data)
        http.new_edge(2, 3, formula.ap("process_data"))
        # PROCESSING -> COMPLETED (complete)
        http.new_edge(3, 4, formula.ap("complete"))
        # COMPLETED -> IDLE (reset)
        http.new_edge(4, 0, formula.ap("reset"))
        # Любое состояние -> ERROR (error или timeout)
        for i in range(len(states) - 1):
            http.new_edge(i, 5, formula.Or(formula.ap("error"), formula.ap("timeout")))
        # ERROR -> IDLE (recovery)
        http.new_edge(5, 0, formula.ap("recovery"))
        
        # Установка начального состояния
        http.set_init_state(0)
        
        # Установка принимающих состояний (COMPLETED)
        http.set_acceptance(4, True)
        
        self.automata['HTTP'] = http
        return http
    
    def create_dns_automaton(self):
        """Создание автомата для DNS протокола"""
        # Состояния DNS
        states = ['IDLE', 'QUERY_SENT', 'RESPONSE_RECEIVED', 'CACHE_LOOKUP', 'RESOLVED', 'ERROR']
        
        # События DNS
        events = ['send_query', 'receive_response', 'cache_hit', 'cache_miss', 'resolve', 'timeout', 'error']
        
        # Создание автомата
        dns = twa_graph()
        dns.set_name("DNS_Protocol")
        
        # Добавление состояний
        for i, state in enumerate(states):
            dns.new_state()
            dns.set_state_name(i, state)
        
        # Добавление переходов
        # IDLE -> QUERY_SENT (send_query)
        dns.new_edge(0, 1, formula.ap("send_query"))
        # IDLE -> CACHE_LOOKUP (cache_lookup)
        dns.new_edge(0, 3, formula.ap("cache_lookup"))
        # QUERY_SENT -> RESPONSE_RECEIVED (receive_response)
        dns.new_edge(1, 2, formula.ap("receive_response"))
        # RESPONSE_RECEIVED -> RESOLVED (resolve)
        dns.new_edge(2, 4, formula.ap("resolve"))
        # CACHE_LOOKUP -> RESOLVED (cache_hit)
        dns.new_edge(3, 4, formula.ap("cache_hit"))
        # CACHE_LOOKUP -> QUERY_SENT (cache_miss)
        dns.new_edge(3, 1, formula.ap("cache_miss"))
        # RESOLVED -> IDLE (reset)
        dns.new_edge(4, 0, formula.ap("reset"))
        # Любое состояние -> ERROR (error или timeout)
        for i in range(len(states) - 1):
            dns.new_edge(i, 5, formula.Or(formula.ap("error"), formula.ap("timeout")))
        # ERROR -> IDLE (recovery)
        dns.new_edge(5, 0, formula.ap("recovery"))
        
        # Установка начального состояния
        dns.set_init_state(0)
        
        # Установка принимающих состояний (RESOLVED)
        dns.set_acceptance(4, True)
        
        self.automata['DNS'] = dns
        return dns
    
    def create_ftp_automaton(self):
        """Создание автомата для FTP протокола"""
        # Состояния FTP
        states = ['IDLE', 'CONNECTING', 'CONNECTED', 'AUTHENTICATING', 'AUTHENTICATED',
                 'TRANSFERRING', 'COMPLETED', 'ERROR']
        
        # События FTP
        events = ['connect', 'connection_established', 'authenticate', 'authentication_success',
                 'start_transfer', 'transfer_complete', 'disconnect', 'timeout', 'error']
        
        # Создание автомата
        ftp = twa_graph()
        ftp.set_name("FTP_Protocol")
        
        # Добавление состояний
        for i, state in enumerate(states):
            ftp.new_state()
            ftp.set_state_name(i, state)
        
        # Добавление переходов
        # IDLE -> CONNECTING (connect)
        ftp.new_edge(0, 1, formula.ap("connect"))
        # CONNECTING -> CONNECTED (connection_established)
        ftp.new_edge(1, 2, formula.ap("connection_established"))
        # CONNECTED -> AUTHENTICATING (authenticate)
        ftp.new_edge(2, 3, formula.ap("authenticate"))
        # AUTHENTICATING -> AUTHENTICATED (authentication_success)
        ftp.new_edge(3, 4, formula.ap("authentication_success"))
        # AUTHENTICATED -> TRANSFERRING (start_transfer)
        ftp.new_edge(4, 5, formula.ap("start_transfer"))
        # TRANSFERRING -> COMPLETED (transfer_complete)
        ftp.new_edge(5, 6, formula.ap("transfer_complete"))
        # COMPLETED -> IDLE (disconnect)
        ftp.new_edge(6, 0, formula.ap("disconnect"))
        # Любое состояние -> ERROR (error или timeout)
        for i in range(len(states) - 1):
            ftp.new_edge(i, 7, formula.Or(formula.ap("error"), formula.ap("timeout")))
        # ERROR -> IDLE (recovery)
        ftp.new_edge(7, 0, formula.ap("recovery"))
        
        # Установка начального состояния
        ftp.set_init_state(0)
        
        # Установка принимающих состояний (COMPLETED)
        ftp.set_acceptance(6, True)
        
        self.automata['FTP'] = ftp
        return ftp
    
    def create_icmp_automaton(self):
        """Создание автомата для ICMP протокола"""
        # Состояния ICMP
        states = ['IDLE', 'ECHO_SENT', 'ECHO_RECEIVED', 'REPLY_SENT', 'COMPLETED', 'ERROR']
        
        # События ICMP
        events = ['send_echo', 'receive_echo', 'send_reply', 'echo_complete', 'timeout', 'error']
        
        # Создание автомата
        icmp = twa_graph()
        icmp.set_name("ICMP_Protocol")
        
        # Добавление состояний
        for i, state in enumerate(states):
            icmp.new_state()
            icmp.set_state_name(i, state)
        
        # Добавление переходов
        # IDLE -> ECHO_SENT (send_echo)
        icmp.new_edge(0, 1, formula.ap("send_echo"))
        # ECHO_SENT -> ECHO_RECEIVED (receive_echo)
        icmp.new_edge(1, 2, formula.ap("receive_echo"))
        # ECHO_RECEIVED -> REPLY_SENT (send_reply)
        icmp.new_edge(2, 3, formula.ap("send_reply"))
        # REPLY_SENT -> COMPLETED (echo_complete)
        icmp.new_edge(3, 4, formula.ap("echo_complete"))
        # COMPLETED -> IDLE (reset)
        icmp.new_edge(4, 0, formula.ap("reset"))
        # Любое состояние -> ERROR (error или timeout)
        for i in range(len(states) - 1):
            icmp.new_edge(i, 5, formula.Or(formula.ap("error"), formula.ap("timeout")))
        # ERROR -> IDLE (recovery)
        icmp.new_edge(5, 0, formula.ap("recovery"))
        
        # Установка начального состояния
        icmp.set_init_state(0)
        
        # Установка принимающих состояний (COMPLETED)
        icmp.set_acceptance(4, True)
        
        self.automata['ICMP'] = icmp
        return icmp
    
    def create_ltl_formulas(self):
        """Создание LTL формул для проверки свойств протоколов"""
        formulas = {}
        
        # TCP формулы
        formulas['TCP_Connection_Establishment'] = formula.Implies(
            formula.And(formula.ap("active_open"), formula.ap("receive_syn_ack")),
            formula.F(formula.ap("ESTABLISHED"))
        )
        
        formulas['TCP_Connection_Teardown'] = formula.Implies(
            formula.ap("send_fin"),
            formula.F(formula.ap("CLOSED"))
        )
        
        formulas['TCP_No_Deadlock'] = formula.G(formula.F(formula.ap("ESTABLISHED")))
        
        # UDP формулы
        formulas['UDP_Reliability'] = formula.Implies(
            formula.ap("send_datagram"),
            formula.F(formula.Or(formula.ap("complete"), formula.ap("error")))
        )
        
        # HTTP формулы
        formulas['HTTP_Request_Response'] = formula.Implies(
            formula.ap("send_request"),
            formula.F(formula.ap("RESPONSE_RECEIVED"))
        )
        
        # DNS формулы
        formulas['DNS_Resolution'] = formula.Implies(
            formula.ap("send_query"),
            formula.F(formula.ap("RESOLVED"))
        )
        
        # FTP формулы
        formulas['FTP_Authentication'] = formula.Implies(
            formula.ap("authenticate"),
            formula.F(formula.ap("AUTHENTICATED"))
        )
        
        # ICMP формулы
        formulas['ICMP_Echo_Reply'] = formula.Implies(
            formula.ap("send_echo"),
            formula.F(formula.ap("ECHO_RECEIVED"))
        )
        
        self.formulas = formulas
        return formulas
    
    def verify_protocol_properties(self, protocol_name):
        """Проверка свойств протокола"""
        if protocol_name not in self.automata:
            print(f"Автомат для протокола {protocol_name} не найден")
            return False
        
        automaton = self.automata[protocol_name]
        
        # Проверка базовых свойств
        print(f"\n=== Проверка свойств протокола {protocol_name} ===")
        
        # Проверка детерминированности
        is_deterministic = automaton.is_deterministic()
        print(f"Детерминированный: {is_deterministic}")
        
        # Проверка завершенности
        is_complete = automaton.is_complete()
        print(f"Завершенный: {is_complete}")
        
        # Проверка минимальности
        is_minimal = automaton.is_minimal()
        print(f"Минимальный: {is_minimal}")
        
        # Количество состояний и переходов
        num_states = automaton.num_states()
        num_edges = automaton.num_edges()
        print(f"Состояний: {num_states}, Переходов: {num_edges}")
        
        return True
    
    def analyze_all_protocols(self):
        """Анализ всех протоколов"""
        print("=== АНАЛИЗ ПРОТОКОЛЬНЫХ АВТОМАТОВ ===")
        
        # Создание всех автоматов
        self.create_tcp_automaton()
        self.create_udp_automaton()
        self.create_http_automaton()
        self.create_dns_automaton()
        self.create_ftp_automaton()
        self.create_icmp_automaton()
        
        # Создание LTL формул
        self.create_ltl_formulas()
        
        # Анализ каждого протокола
        for protocol_name in self.automata.keys():
            self.verify_protocol_properties(protocol_name)
        
        # Вывод LTL формул
        print("\n=== LTL ФОРМУЛЫ ===")
        for name, formula_obj in self.formulas.items():
            print(f"{name}: {formula_obj}")
    
    def export_automata(self, format_type="dot"):
        """Экспорт автоматов в различные форматы"""
        for name, automaton in self.automata.items():
            filename = f"{name.lower()}_automaton.{format_type}"
            try:
                if format_type == "dot":
                    with open(filename, 'w') as f:
                        automaton.to_str(format_type, f)
                elif format_type == "hoa":
                    with open(filename, 'w') as f:
                        automaton.to_str(format_type, f)
                print(f"Автомат {name} экспортирован в {filename}")
            except Exception as e:
                print(f"Ошибка экспорта {name}: {e}")

def main():
    """Главная функция"""
    print("Создание и анализ протокольных автоматов с помощью Spot")
    
    # Создание экземпляра класса
    protocol_analyzer = ProtocolAutomata()
    
    # Анализ всех протоколов
    protocol_analyzer.analyze_all_protocols()
    
    # Экспорт автоматов
    print("\n=== ЭКСПОРТ АВТОМАТОВ ===")
    protocol_analyzer.export_automata("dot")
    
    print("\nАнализ завершен!")

if __name__ == "__main__":
    main()


