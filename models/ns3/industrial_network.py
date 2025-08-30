#!/usr/bin/env python3
"""
NS-3 модель промышленной сети
Промышленные протоколы: Modbus TCP, EtherCAT
Автор: Senior Developer
Дата: 2024-12-19
"""

import ns.core
import ns.network
import ns.internet
import ns.applications
import ns.point_to_point
import ns.csma
import ns.flow_monitor
import ns.flow_monitor_helper

def create_industrial_network():
    """
    Создает модель промышленной сети с NS-3
    Включает: PLC, HMI, датчики, исполнительные механизмы
    """
    
    # Включение логирования
    ns.core.LogComponentEnable("UdpEchoClientApplication", ns.core.LOG_LEVEL_INFO)
    ns.core.LogComponentEnable("UdpEchoServerApplication", ns.core.LOG_LEVEL_INFO)
    
    # Создание узлов
    print("Создание узлов промышленной сети...")
    
    # PLC (Programmable Logic Controller) - центральный узел
    plc_node = ns.network.Node()
    
    # HMI (Human Machine Interface) - интерфейс оператора
    hmi_node = ns.network.Node()
    
    # Датчики (сенсоры)
    sensor_nodes = []
    for i in range(3):
        sensor_nodes.append(ns.network.Node())
    
    # Исполнительные механизмы (актуаторы)
    actuator_nodes = []
    for i in range(2):
        actuator_nodes.append(ns.network.Node())
    
    # Создание каналов связи
    print("Создание каналов связи...")
    
    # Высокоскоростной канал PLC-HMI (100 Mbps)
    plc_hmi_channel = ns.point_to_point.PointToPointHelper()
    plc_hmi_channel.SetDeviceAttribute("DataRate", ns.core.StringValue("100Mbps"))
    plc_hmi_channel.SetChannelAttribute("Delay", ns.core.StringValue("1ms"))
    
    plc_hmi_devices = plc_hmi_channel.Install(plc_node, hmi_node)
    
    # CSMA канал для датчиков (10 Mbps)
    sensor_channel = ns.csma.CsmaHelper()
    sensor_channel.SetChannelAttribute("DataRate", ns.core.StringValue("10Mbps"))
    sensor_channel.SetChannelAttribute("Delay", ns.core.StringValue("2ms"))
    
    sensor_devices = sensor_channel.Install([plc_node] + sensor_nodes)
    
    # CSMA канал для исполнительных механизмов (10 Mbps)
    actuator_channel = ns.csma.CsmaHelper()
    actuator_channel.SetChannelAttribute("DataRate", ns.core.StringValue("10Mbps"))
    actuator_channel.SetChannelAttribute("Delay", ns.core.StringValue("2ms"))
    
    actuator_devices = actuator_channel.Install([plc_node] + actuator_nodes)
    
    # Установка стека TCP/IP
    print("Установка стека TCP/IP...")
    internet = ns.internet.InternetStackHelper()
    internet.Install([plc_node, hmi_node] + sensor_nodes + actuator_nodes)
    
    # Назначение IP адресов
    print("Назначение IP адресов...")
    
    # PLC-HMI сеть (192.168.1.0/24)
    plc_hmi_ip = ns.internet.Ipv4AddressHelper("192.168.1.0", "255.255.255.0")
    plc_hmi_ip.Assign(plc_hmi_devices)
    
    # Сеть датчиков (192.168.2.0/24)
    sensor_ip = ns.internet.Ipv4AddressHelper("192.168.2.0", "255.255.255.0")
    sensor_ip.Assign(sensor_devices)
    
    # Сеть исполнительных механизмов (192.168.3.0/24)
    actuator_ip = ns.internet.Ipv4AddressHelper("192.168.3.0", "255.255.255.0")
    actuator_ip.Assign(actuator_devices)
    
    # Создание приложений
    print("Создание промышленных приложений...")
    
    # Modbus TCP сервер на PLC
    modbus_server = ns.applications.PacketSinkHelper("ns3::TcpSocketFactory", 
                                                   ns.network.InetSocketAddress(ns.network.Ipv4Address.GetAny(), 502))
    modbus_server_app = modbus_server.Install(plc_node)
    modbus_server_app.Start(ns.core.Seconds(1.0))
    modbus_server_app.Stop(ns.core.Seconds(100.0))
    
    # Modbus TCP клиенты на датчиках
    modbus_clients = []
    for i, sensor_node in enumerate(sensor_nodes):
        # Получение IP адреса PLC
        plc_ip = plc_node.GetObject(ns.internet.Ipv4.GetTypeId()).GetAddress(1, 0).GetLocal()
        
        modbus_client = ns.applications.OnOffHelper("ns3::TcpSocketFactory", 
                                                  ns.network.InetSocketAddress(plc_ip, 502))
        modbus_client.SetAttribute("PacketSize", ns.core.UintegerValue(1024))
        modbus_client.SetAttribute("DataRate", ns.core.StringValue("1Mbps"))
        modbus_client.SetAttribute("OnTime", ns.core.StringValue("ns3::ConstantRandomVariable[Constant=1]"))
        modbus_client.SetAttribute("OffTime", ns.core.StringValue("ns3::ConstantRandomVariable[Constant=0]"))
        
        modbus_client_app = modbus_client.Install(sensor_node)
        modbus_client_app.Start(ns.core.Seconds(2.0 + i))
        modbus_client_app.Stop(ns.core.Seconds(98.0))
        modbus_clients.append(modbus_client_app)
    
    # EtherCAT мастер на PLC (симуляция через UDP)
    ethercat_master = ns.applications.UdpEchoServerHelper(34980)
    ethercat_master_app = ethercat_master.Install(plc_node)
    ethercat_master_app.Start(ns.core.Seconds(1.0))
    ethercat_master_app.Stop(ns.core.Seconds(100.0))
    
    # EtherCAT слейвы на исполнительных механизмах
    ethercat_slaves = []
    for i, actuator_node in enumerate(actuator_nodes):
        # Получение IP адреса PLC
        plc_ip = plc_node.GetObject(ns.internet.Ipv4.GetTypeId()).GetAddress(1, 0).GetLocal()
        
        ethercat_slave = ns.applications.UdpEchoClientHelper(plc_ip, 34980)
        ethercat_slave.SetAttribute("MaxPackets", ns.core.UintegerValue(100))
        ethercat_slave.SetAttribute("Interval", ns.core.TimeValue(ns.core.Seconds(0.1)))
        ethercat_slave.SetAttribute("PacketSize", ns.core.UintegerValue(1024))
        
        ethercat_slave_app = ethercat_slave.Install(actuator_node)
        ethercat_slave_app.Start(ns.core.Seconds(2.0 + i))
        ethercat_slave_app.Stop(ns.core.Seconds(98.0))
        ethercat_slaves.append(ethercat_slave_app)
    
    # HMI приложение (HTTP клиент)
    plc_ip = plc_node.GetObject(ns.internet.Ipv4.GetTypeId()).GetAddress(1, 0).GetLocal()
    hmi_client = ns.applications.OnOffHelper("ns3::TcpSocketFactory", 
                                           ns.network.InetSocketAddress(plc_ip, 80))
    hmi_client.SetAttribute("PacketSize", ns.core.UintegerValue(1024))
    hmi_client.SetAttribute("DataRate", ns.core.StringValue("10Mbps"))
    hmi_client.SetAttribute("OnTime", ns.core.StringValue("ns3::ConstantRandomVariable[Constant=1]"))
    hmi_client.SetAttribute("OffTime", ns.core.StringValue("ns3::ConstantRandomVariable[Constant=0]"))
    
    hmi_client_app = hmi_client.Install(hmi_node)
    hmi_client_app.Start(ns.core.Seconds(3.0))
    hmi_client_app.Stop(ns.core.Seconds(97.0))
    
    # Мониторинг потоков
    print("Настройка мониторинга потоков...")
    flow_monitor = ns.flow_monitor.FlowMonitorHelper()
    monitor = flow_monitor.InstallAll()
    
    # Запуск симуляции
    print("Запуск симуляции промышленной сети...")
    print("Длительность: 100 секунд")
    print("Узлы: 1 PLC + 1 HMI + 3 датчика + 2 исполнительных механизма")
    
    ns.core.Simulator.Run()
    
    # Анализ результатов
    print("\n=== РЕЗУЛЬТАТЫ СИМУЛЯЦИИ ===")
    
    # Статистика потоков
    monitor.CheckForLostPackets()
    classifier = flow_monitor.GetClassifier()
    
    if monitor.GetFlowStats():
        for flow_id, flow_stats in monitor.GetFlowStats():
            if flow_id == 0:
                continue
                
            t = classifier.FindFlow(flow_id)
            proto = {6: 'TCP', 17: 'UDP'}[t.protocol]
            src = t.sourceAddress
            dst = t.destinationAddress
            
            print(f"Поток {flow_id}: {src} -> {dst} ({proto})")
            print(f"  Пакетов: {flow_stats.txPackets} -> {flow_stats.rxPackets}")
            print(f"  Байт: {flow_stats.txBytes} -> {flow_stats.rxBytes}")
            print(f"  Задержка: {flow_stats.delaySum.GetSeconds() / flow_stats.rxPackets:.3f} сек")
            print(f"  Потери: {flow_stats.lostPackets}")
            print()
    
    # Сохранение результатов
    monitor.SerializeToXmlFile("ns3_industrial_network.xml", True, True)
    
    print("Симуляция завершена. Результаты сохранены в ns3_industrial_network.xml")
    
    ns.core.Simulator.Destroy()

if __name__ == "__main__":
    # Настройка NS-3
    ns.core.GlobalValue.Bind("SimulatorImplementationType", 
                            ns.core.StringValue("ns3::DefaultSimulatorImpl"))
    
    # Запуск симуляции
    create_industrial_network()

