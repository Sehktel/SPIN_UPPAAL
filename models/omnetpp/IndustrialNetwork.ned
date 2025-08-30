// OMNeT++ NED модель промышленной сети
// Промышленные протоколы: Modbus TCP, EtherCAT, OPC UA
// Автор: Senior Developer
// Дата: 2024-12-19

package industrial_network;

import ned.DatarateChannel;
import industrial_network.modules.*;

// Главная сеть промышленной системы
network IndustrialNetwork
{
    parameters:
        // Параметры сети
        int num_sensors = default(3);
        int num_actuators = default(2);
        double plc_cycle_time = default(1ms);
        double sensor_update_rate = default(100ms);
        double actuator_response_time = default(10ms);
        
        // Сетевые параметры
        double ethernet_bandwidth = default(100Mbps);
        double modbus_timeout = default(1000ms);
        double ethercat_cycle_time = default(1ms);
        double opc_ua_publish_interval = default(100ms);
        
        // Параметры протоколов
        bool modbus_enabled = default(true);
        bool ethercat_enabled = default(true);
        bool opc_ua_enabled = default(true);
        
        @display("bgb=800,600");
        
    submodules:
        // Центральный контроллер (PLC)
        plc: PLC {
            @display("p=400,300");
        }
        
        // Интерфейс оператора (HMI)
        hmi: HMI {
            @display("p=600,200");
        }
        
        // Датчики (сенсоры)
        sensors[num_sensors]: Sensor {
            @display("p=200,200");
        }
        
        // Исполнительные механизмы (актуаторы)
        actuators[num_actuators]: Actuator {
            @display("p=200,400");
        }
        
        // Промышленный коммутатор
        switch: IndustrialSwitch {
            @display("p=400,200");
        }
        
        // Модем для удаленного доступа
        modem: Modem {
            @display("p=600,400");
        }
        
    connections:
        // Высокоскоростное соединение PLC-HMI
        plc.out++ --> {delay = 1ms} --> hmi.in++;
        hmi.out++ --> {delay = 1ms} --> plc.in++;
        
        // PLC к коммутатору
        plc.out++ --> {delay = 0.5ms} --> switch.in++;
        switch.out++ --> {delay = 0.5ms} --> plc.in++;
        
        // Коммутатор к датчикам
        switch.out++ --> {delay = 2ms} --> sensors[*].in++;
        sensors[*].out++ --> {delay = 2ms} --> switch.in++;
        
        // Коммутатор к исполнительным механизмам
        switch.out++ --> {delay = 2ms} --> actuators[*].in++;
        actuators[*].out++ --> {delay = 2ms} --> switch.in++;
        
        // PLC к модему (удаленный доступ)
        plc.out++ --> {delay = 5ms} --> modem.in++;
        modem.out++ --> {delay = 5ms} --> plc.in++;
}

// Модуль PLC (Programmable Logic Controller)
module PLC
{
    parameters:
        double cycle_time = default(1ms);
        bool modbus_server = default(true);
        bool ethercat_master = default(true);
        bool opc_ua_server = default(true);
        
        @display("i=device/pc");
        
    gates:
        input in[];
        output out[];
        
    submodules:
        // Процессор PLC
        cpu: PLCProcessor {
            @display("p=0,0");
        }
        
        // Память PLC
        memory: PLCMemory {
            @display("p=0,50");
        }
        
        // Сетевой интерфейс
        network_if: NetworkInterface {
            @display("p=0,100");
        }
        
        // Modbus TCP сервер
        modbus_server: ModbusTCPServer if modbus_server {
            @display("p=0,150");
        }
        
        // EtherCAT мастер
        ethercat_master: EtherCATMaster if ethercat_master {
            @display("p=0,200");
        }
        
        // OPC UA сервер
        opc_ua_server: OPCUAServer if opc_ua_server {
            @display("p=0,250");
        }
        
    connections:
        // Внутренние соединения PLC
        cpu.out --> memory.in;
        memory.out --> network_if.in;
        network_if.out --> modbus_server.in;
        network_if.out --> ethercat_master.in;
        network_if.out --> opc_ua_server.in;
        
        // Внешние соединения
        in --> network_if.in;
        network_if.out --> out;
}

// Модуль HMI (Human Machine Interface)
module HMI
{
    parameters:
        bool web_interface = default(true);
        bool scada_client = default(true);
        
        @display("i=device/laptop");
        
    gates:
        input in[];
        output out[];
        
    submodules:
        // Веб-интерфейс
        web_ui: WebInterface if web_interface {
            @display("p=0,0");
        }
        
        // SCADA клиент
        scada: SCADAClient if scada_client {
            @display("p=0,50");
        }
        
        // Сетевой интерфейс
        network_if: NetworkInterface {
            @display("p=0,100");
        }
        
    connections:
        web_ui.out --> network_if.in;
        scada.out --> network_if.in;
        network_if.out --> out;
        in --> network_if.in;
}

// Модуль датчика (сенсора)
module Sensor
{
    parameters:
        string sensor_type = default("temperature");
        double update_rate = default(100ms);
        double accuracy = default(0.1);
        
        @display("i=device/sensor");
        
    gates:
        input in[];
        output out[];
        
    submodules:
        // Сенсорный элемент
        sensor_element: SensorElement {
            @display("p=0,0");
        }
        
        // АЦП (аналого-цифровой преобразователь)
        adc: ADC {
            @display("p=0,50");
        }
        
        // Сетевой интерфейс
        network_if: NetworkInterface {
            @display("p=0,100");
        }
        
        // Modbus TCP клиент
        modbus_client: ModbusTCPClient {
            @display("p=0,150");
        }
        
    connections:
        sensor_element.out --> adc.in;
        adc.out --> network_if.in;
        network_if.out --> modbus_client.in;
        modbus_client.out --> out;
        in --> network_if.in;
}

// Модуль исполнительного механизма (актуатора)
module Actuator
{
    parameters:
        string actuator_type = default("valve");
        double response_time = default(10ms);
        double max_force = default(1000N);
        
        @display("i=device/actuator");
        
    gates:
        input in[];
        output out[];
        
    submodules:
        // ЦАП (цифро-аналоговый преобразователь)
        dac: DAC {
            @display("p=0,0");
        }
        
        // Исполнительный элемент
        actuator_element: ActuatorElement {
            @display("p=0,50");
        }
        
        // Сетевой интерфейс
        network_if: NetworkInterface {
            @display("p=0,100");
        }
        
        // EtherCAT слейв
        ethercat_slave: EtherCATSlave {
            @display("p=0,150");
        }
        
    connections:
        network_if.out --> ethercat_slave.in;
        ethercat_slave.out --> dac.in;
        dac.out --> actuator_element.in;
        actuator_element.out --> out;
        in --> network_if.in;
}

// Промышленный коммутатор
module IndustrialSwitch
{
    parameters:
        int num_ports = default(8);
        double switching_delay = default(1us);
        
        @display("i=device/switch");
        
    gates:
        input in[];
        output out[];
        
    submodules:
        // Коммутационная матрица
        switch_matrix: SwitchMatrix {
            @display("p=0,0");
        }
        
        // Буферы портов
        port_buffers[num_ports]: PortBuffer {
            @display("p=0,50");
        }
        
    connections:
        in --> switch_matrix.in;
        switch_matrix.out --> out;
}

// Модем для удаленного доступа
module Modem
{
    parameters:
        double baud_rate = default(9600);
        bool encryption = default(true);
        
        @display("i=device/modem");
        
    gates:
        input in[];
        output out[];
        
    submodules:
        // Модемный интерфейс
        modem_if: ModemInterface {
            @display("p=0,0");
        }
        
        // Шифрование
        encryption_module: Encryption if encryption {
            @display("p=0,50");
        }
        
    connections:
        in --> modem_if.in;
        modem_if.out --> encryption_module.in;
        encryption_module.out --> out;
}

// Вспомогательные модули (заглушки)
module PLCProcessor { gates: input in; output out; }
module PLCMemory { gates: input in; output out; }
module NetworkInterface { gates: input in; output out; }
module ModbusTCPServer { gates: input in; output out; }
module EtherCATMaster { gates: input in; output out; }
module OPCUAServer { gates: input in; output out; }
module WebInterface { gates: input in; output out; }
module SCADAClient { gates: input in; output out; }
module SensorElement { gates: input in; output out; }
module ADC { gates: input in; output out; }
module ModbusTCPClient { gates: input in; output out; }
module DAC { gates: input in; output out; }
module ActuatorElement { gates: input in; output out; }
module EtherCATSlave { gates: input in; output out; }
module SwitchMatrix { gates: input in[]; output out[]; }
module PortBuffer { gates: input in; output out; }
module ModemInterface { gates: input in; output out; }
module Encryption { gates: input in; output out; }

