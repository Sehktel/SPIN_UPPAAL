/*
 * Модель протокола EtherCAT в SPIN
 * 
 * EtherCAT (Ethernet for Control Automation Technology) - 
 * высокоскоростная полевая сеть для промышленной автоматизации
 * 
 * Архитектура:
 * - EtherCATMaster: мастер, управляющий сетью
 * - EtherCATSlave: слейвы, обрабатывающие команды
 * - EtherCATNetwork: сеть, маршрутизирующая фреймы
 * 
 * Особенности:
 * - Мастер-слейв архитектура
 * - Состояния слейвов: INIT, PRE_OP, SAFE_OP, OP
 * - Обработка фреймов "on-the-fly"
 * - Синхронизация и безопасность
 */

// Типы команд EtherCAT
#define CMD_LRW    1  // Logical Read Write
#define CMD_LRD    2  // Logical Read
#define CMD_LWR    3  // Logical Write
#define CMD_APRD   4  // Auto Increment Physical Read
#define CMD_APWR   5  // Auto Increment Physical Write
#define CMD_FPRD   6  // Configured Address Physical Read
#define CMD_FPWR   7  // Configured Address Physical Write

// Состояния слейва
#define STATE_INIT     0
#define STATE_PRE_OP   1
#define STATE_SAFE_OP  2
#define STATE_OP       3
#define STATE_ERROR    4

// Статусы операций
#define STATUS_OK      0
#define STATUS_ERROR   1
#define STATUS_TIMEOUT 2

// Структура EtherCAT фрейма
typedef EtherCATFrame {
    byte command;      // Тип команды
    byte address;      // Адрес слейва
    byte data[64];     // Данные
    byte length;       // Длина данных
    byte status;       // Статус выполнения
}

// Глобальные переменные для отслеживания состояния
int master_state = 0;           // 0: IDLE, 1: RUNNING, 2: ERROR
int slave_states[3] = {0, 0, 0}; // Состояния 3 слейвов
int network_ready = 0;          // Сеть готова к работе
int cycle_count = 0;            // Счетчик циклов
int frames_sent = 0;            // Фреймы отправлены
int frames_received = 0;        // Фреймы получены
int frames_processed = 0;       // Фреймы обработаны

// Каналы для коммуникации
chan master_to_network = [1] of {EtherCATFrame};
chan network_to_slave = [3] of {EtherCATFrame};  // 3 слейва
chan slave_to_network = [3] of {EtherCATFrame};  // 3 слейва
chan network_to_master = [1] of {EtherCATFrame};

// Процесс EtherCAT Master
proctype EtherCATMaster() {
    EtherCATFrame frame;
    byte slave_addr;
    
    printf("Мастер: Инициализация EtherCAT сети\n");
    master_state = 0; // IDLE
    
    // Инициализация сети
    printf("Мастер: Проверка готовности сети\n");
    network_ready = 1;
    
    // Переход в состояние RUNNING
    printf("Мастер: Переход в состояние RUNNING\n");
    master_state = 1;
    
    do
    :: master_state == 1 -> { // RUNNING
        // Создаем команду для слейва
        slave_addr = (cycle_count % 3); // Циклически по слейвам
        
        frame.command = CMD_LRW;
        frame.address = slave_addr;
        frame.data[0] = cycle_count;
        frame.length = 1;
        frame.status = STATUS_OK;
        
        printf("Мастер: Отправляю команду LRW слейву %d, данные: %d\n", 
               slave_addr, frame.data[0]);
        
        master_to_network!frame;
        frames_sent++;
        
        // Ожидаем ответ
        network_to_master?frame;
        if
        :: frame.status == STATUS_OK -> {
            printf("Мастер: Получен успешный ответ от слейва %d\n", frame.address);
            frames_received++;
            cycle_count++;
        }
        :: frame.status == STATUS_ERROR -> {
            printf("Мастер: Ошибка от слейва %d\n", frame.address);
            master_state = 2; // ERROR
        }
        :: frame.status == STATUS_TIMEOUT -> {
            printf("Мастер: Таймаут от слейва %d\n", frame.address);
            master_state = 2; // ERROR
        }
        fi;
        
        // Проверяем состояние сети
        if
        :: cycle_count > 100 -> {
            printf("Мастер: Завершение работы после 100 циклов\n");
            break;
        }
        :: else -> {
            // Продолжаем работу
        }
        fi;
    }
    :: master_state == 2 -> { // ERROR
        printf("Мастер: Обработка ошибки\n");
        // Попытка восстановления
        master_state = 1; // Возврат в RUNNING
    }
    od;
    
    printf("Мастер: Завершение работы\n");
}

// Процесс EtherCAT Slave
proctype EtherCATSlave(byte slave_id) {
    EtherCATFrame frame;
    byte current_state;
    
    printf("Слейв %d: Инициализация\n", slave_id);
    current_state = STATE_INIT;
    slave_states[slave_id] = current_state;
    
    // Инициализация
    printf("Слейв %d: Переход в PRE_OP\n", slave_id);
    current_state = STATE_PRE_OP;
    slave_states[slave_id] = current_state;
    
    // Проверка конфигурации
    printf("Слейв %d: Переход в SAFE_OP\n", slave_id);
    current_state = STATE_SAFE_OP;
    slave_states[slave_id] = current_state;
    
    // Проверка безопасности
    printf("Слейв %d: Переход в OP\n", slave_id);
    current_state = STATE_OP;
    slave_states[slave_id] = current_state;
    
    do
    :: current_state == STATE_OP -> {
        // Ожидаем команды от сети
        network_to_slave[slave_id]?frame;
        
        if
        :: frame.address == slave_id -> {
            printf("Слейв %d: Получена команда %d\n", slave_id, frame.command);
            frames_processed++;
            
            // Обработка команды в зависимости от типа
            if
            :: frame.command == CMD_LRW -> {
                printf("Слейв %d: Обрабатываю LRW\n", slave_id);
                // Читаем данные, записываем новые
                frame.data[0] = frame.data[0] + 100; // Симуляция обработки
                frame.status = STATUS_OK;
            }
            :: frame.command == CMD_LRD -> {
                printf("Слейв %d: Обрабатываю LRD\n", slave_id);
                // Читаем данные
                frame.data[0] = slave_id * 10 + cycle_count;
                frame.status = STATUS_OK;
            }
            :: frame.command == CMD_LWR -> {
                printf("Слейв %d: Обрабатываю LWR\n", slave_id);
                // Записываем данные
                frame.status = STATUS_OK;
            }
            :: else -> {
                printf("Слейв %d: Неизвестная команда %d\n", slave_id, frame.command);
                frame.status = STATUS_ERROR;
            }
            fi;
            
            // Отправляем ответ
            printf("Слейв %d: Отправляю ответ, статус: %d\n", slave_id, frame.status);
            slave_to_network[slave_id]!frame;
        }
        :: else -> {
            printf("Слейв %d: Команда не для меня (адрес: %d)\n", slave_id, frame.address);
            // Передаем фрейм дальше (имитация "on-the-fly" обработки)
            network_to_slave[(slave_id + 1) % 3]!frame;
        }
        fi;
    }
    :: current_state == STATE_ERROR -> {
        printf("Слейв %d: В состоянии ERROR\n", slave_id);
        // Попытка восстановления
        current_state = STATE_INIT;
        slave_states[slave_id] = current_state;
    }
    od;
}

// Процесс EtherCAT Network
proctype EtherCATNetwork() {
    EtherCATFrame frame;
    byte source, target;
    
    printf("Сеть: Инициализация EtherCAT сети\n");
    
    do
    :: network_ready == 1 -> {
        // Ожидаем фреймы от мастера
        master_to_network?frame;
        printf("Сеть: Получен фрейм от мастера для слейва %d\n", frame.address);
        
        // Маршрутизация к слейву
        target = frame.address;
        if
        :: target < 3 -> {
            printf("Сеть: Передаю фрейм слейву %d\n", target);
            network_to_slave[target]!frame;
        }
        :: else -> {
            printf("Сеть: Неверный адрес слейва %d\n", target);
            frame.status = STATUS_ERROR;
            network_to_master!frame;
        }
        fi;
        
        // Ожидаем ответы от слейвов
        if
        :: slave_to_network[0]?frame -> {
            printf("Сеть: Получен ответ от слейва 0\n");
            network_to_master!frame;
        }
        :: slave_to_network[1]?frame -> {
            printf("Сеть: Получен ответ от слейва 1\n");
            network_to_master!frame;
        }
        :: slave_to_network[2]?frame -> {
            printf("Сеть: Получен ответ от слейва 2\n");
            network_to_master!frame;
        }
        fi;
    }
    od;
}

// Инициализация системы
init {
    printf("=== Инициализация EtherCAT системы ===\n");
    
    // Запускаем все процессы
    run EtherCATMaster();
    run EtherCATSlave(0);
    run EtherCATSlave(1);
    run EtherCATSlave(2);
    run EtherCATNetwork();
    
    printf("=== Все процессы запущены ===\n");
}

// LTL свойства для верификации

// Безопасность: слейв не может перейти в OP без прохождения всех предыдущих состояний
ltl state_progression { 
    [] (slave_states[0] == STATE_OP -> 
        (slave_states[0] == STATE_INIT && 
         slave_states[0] == STATE_PRE_OP && 
         slave_states[0] == STATE_SAFE_OP)) 
}

// Безопасность: команды выполняются только в состоянии OP
ltl command_in_op_state { 
    [] (frames_processed > 0 -> slave_states[0] == STATE_OP) 
}

// Живость: мастер может достичь состояния RUNNING
ltl master_can_run { 
    <> master_state == 1 
}

// Живость: слейв может достичь состояния OP
ltl slave_can_reach_op { 
    <> slave_states[0] == STATE_OP 
}

// Отсутствие тупиков: система не может заблокироваться
ltl no_deadlock { 
    [] <> (master_state == 1 || master_state == 2) 
}

// Синхронизация: мастер и слейвы работают синхронно
ltl synchronization { 
    [] (master_state == 1 -> slave_states[0] == STATE_OP) 
}

// Безопасность сети: фреймы не теряются
ltl no_frame_loss { 
    [] (frames_sent == frames_received) 
}

// Корректность обработки: все команды обрабатываются
ltl command_processing { 
    [] (frames_received > 0 -> frames_processed > 0) 
}
