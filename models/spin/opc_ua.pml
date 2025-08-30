/*
 * Модель протокола OPC UA в SPIN
 * Фокус на безопасности и многоуровневой архитектуре
 * 
 * OPC UA (OPC Unified Architecture) - промышленный протокол
 * для безопасной передачи данных в IoT и промышленных системах
 * 
 * Архитектура:
 * - Client: клиент OPC UA
 * - Server: сервер OPC UA  
 * - SecurityLayer: уровень безопасности (аутентификация, авторизация)
 * - TransportLayer: транспортный уровень (TCP, шифрование)
 * - SessionManager: управление сеансами
 */

// Глобальные переменные для отслеживания состояния
int client_authenticated = 0;      // Клиент аутентифицирован
int client_authorized = 0;         // Клиент авторизован
int session_established = 0;       // Сеанс установлен
int secure_channel_open = 0;       // Безопасный канал открыт
int message_encrypted = 0;         // Сообщение зашифровано
int message_sent = 0;              // Сообщение отправлено
int message_received = 0;          // Сообщение получено
int response_sent = 0;             // Ответ отправлен
int response_received = 0;         // Ответ получен
int session_closed = 0;            // Сеанс закрыт

// Каналы для коммуникации между уровнями
chan client_to_security = [1] of {int, int};    // Клиент -> Безопасность
chan security_to_transport = [1] of {int, int}; // Безопасность -> Транспорт
chan transport_to_server = [1] of {int, int};   // Транспорт -> Сервер
chan server_to_transport = [1] of {int, int};   // Сервер -> Транспорт
chan transport_to_security = [1] of {int, int}; // Транспорт -> Безопасность
chan security_to_client = [1] of {int, int};   // Безопасность -> Клиент

// Константы для типов сообщений
#define MSG_CONNECT     1
#define MSG_AUTH        2
#define MSG_REQUEST     3
#define MSG_RESPONSE    4
#define MSG_DISCONNECT 5

// Константы для статусов
#define STATUS_OK       0
#define STATUS_AUTH_FAIL 1
#define STATUS_AUTH_REQ  2
#define STATUS_ERROR     3

// Процесс клиента OPC UA
proctype OPCUAClient() {
    int msg_type, msg_data;
    
    // Шаг 1: Попытка подключения
    printf("Клиент: Отправляю запрос на подключение\n");
    client_to_security!MSG_CONNECT, 0;
    
    // Шаг 2: Ожидание ответа по безопасности
    security_to_client?msg_type, msg_data;
    
    if
    :: msg_type == MSG_AUTH && msg_data == STATUS_AUTH_REQ -> {
        printf("Клиент: Получен запрос на аутентификацию\n");
        client_authenticated = 1;
        
        // Отправляем учетные данные
        client_to_security!MSG_AUTH, 12345; // ID пользователя
        security_to_client?msg_type, msg_data;
        
        if
        :: msg_type == MSG_AUTH && msg_data == STATUS_OK -> {
            printf("Клиент: Аутентификация успешна\n");
            client_authorized = 1;
            
            // Отправляем рабочий запрос
            printf("Клиент: Отправляю рабочий запрос\n");
            client_to_security!MSG_REQUEST, 100;
            
            // Ожидаем ответ
            security_to_client?msg_type, msg_data;
            if
            :: msg_type == MSG_RESPONSE -> {
                printf("Клиент: Получен ответ: %d\n", msg_data);
                response_received = 1;
            }
            :: else -> {
                printf("Клиент: Неожиданный тип сообщения: %d\n", msg_type);
            }
            fi;
        }
        :: msg_type == MSG_AUTH && msg_data == STATUS_AUTH_FAIL -> {
            printf("Клиент: Аутентификация не удалась\n");
        }
        :: else -> {
            printf("Клиент: Неожиданный ответ: %d, %d\n", msg_type, msg_data);
        }
        fi;
    }
    :: msg_type == MSG_AUTH && msg_data == STATUS_AUTH_FAIL -> {
        printf("Клиент: Подключение отклонено\n");
    }
    :: else -> {
        printf("Клиент: Неожиданный ответ: %d, %d\n", msg_type, msg_data);
    }
    fi;
    
    // Закрытие соединения
    printf("Клиент: Закрываю соединение\n");
    client_to_security!MSG_DISCONNECT, 0;
}

// Процесс уровня безопасности
proctype SecurityLayer() {
    int msg_type, msg_data;
    int user_id;
    
    // Ожидаем сообщения от клиента
    client_to_security?msg_type, msg_data;
    
    if
    :: msg_type == MSG_CONNECT -> {
        printf("Безопасность: Получен запрос на подключение\n");
        // Требуем аутентификацию
        security_to_client!MSG_AUTH, STATUS_AUTH_REQ;
        
        // Ожидаем учетные данные
        client_to_security?msg_type, user_id;
        if
        :: msg_type == MSG_AUTH -> {
            // Проверяем учетные данные (упрощенно)
            if
            :: user_id == 12345 -> {
                printf("Безопасность: Аутентификация успешна для пользователя %d\n", user_id);
                session_established = 1;
                security_to_client!MSG_AUTH, STATUS_OK;
                
                // Ожидаем рабочий запрос
                client_to_security?msg_type, msg_data;
                if
                :: msg_type == MSG_REQUEST -> {
                    printf("Безопасность: Передаю запрос на транспорт\n");
                    message_encrypted = 1;
                    security_to_transport!msg_type, msg_data;
                    
                    // Ожидаем ответ от транспорта
                    transport_to_security?msg_type, msg_data;
                    if
                    :: msg_type == MSG_RESPONSE -> {
                        printf("Безопасность: Передаю ответ клиенту\n");
                        security_to_client!MSG_RESPONSE, msg_data;
                    }
                    :: else -> {
                        printf("Безопасность: Ошибка транспорта: %d\n", msg_type);
                    }
                    fi;
                }
                :: msg_type == MSG_DISCONNECT -> {
                    printf("Безопасность: Клиент отключается\n");
                    session_closed = 1;
                }
                :: else -> {
                    printf("Безопасность: Неожиданный запрос: %d\n", msg_type);
                }
                fi;
            }
            :: else -> {
                printf("Безопасность: Аутентификация не удалась для пользователя %d\n", user_id);
                security_to_client!MSG_AUTH, STATUS_AUTH_FAIL;
            }
            fi;
        }
        :: else -> {
            printf("Безопасность: Ожидался запрос аутентификации, получен: %d\n", msg_type);
        }
        fi;
    }
    :: else -> {
        printf("Безопасность: Неожиданный тип сообщения: %d\n", msg_type);
    }
    fi;
}

// Процесс транспортного уровня
proctype TransportLayer() {
    int msg_type, msg_data;
    
    // Ожидаем сообщения от уровня безопасности
    security_to_transport?msg_type, msg_data;
    
    if
    :: msg_type == MSG_REQUEST -> {
        printf("Транспорт: Получен запрос, открываю безопасный канал\n");
        secure_channel_open = 1;
        
        // Передаем запрос серверу
        printf("Транспорт: Передаю запрос серверу\n");
        transport_to_server!msg_type, msg_data;
        message_sent = 1;
        
        // Ожидаем ответ от сервера
        server_to_transport?msg_type, msg_data;
        if
        :: msg_type == MSG_RESPONSE -> {
            printf("Транспорт: Получен ответ от сервера\n");
            message_received = 1;
            
            // Передаем ответ обратно
            printf("Транспорт: Передаю ответ на уровень безопасности\n");
            transport_to_security!MSG_RESPONSE, msg_data;
            response_sent = 1;
        }
        :: else -> {
            printf("Транспорт: Неожиданный ответ от сервера: %d\n", msg_type);
        }
        fi;
    }
    :: else -> {
        printf("Транспорт: Неожиданный тип сообщения: %d\n", msg_type);
    }
    fi;
}

// Процесс сервера OPC UA
proctype OPCUAServer() {
    int msg_type, msg_data;
    
    // Ожидаем запросы от транспортного уровня
    transport_to_server?msg_type, msg_data;
    
    if
    :: msg_type == MSG_REQUEST -> {
        printf("Сервер: Получен запрос: %d\n", msg_data);
        
        // Обрабатываем запрос (упрощенно)
        if
        :: msg_data == 100 -> {
            printf("Сервер: Обрабатываю запрос чтения данных\n");
            // Симулируем обработку
            msg_data = 200; // Результат
        }
        :: else -> {
            printf("Сервер: Неизвестный тип запроса: %d\n", msg_data);
            msg_data = STATUS_ERROR;
        }
        fi;
        
        // Отправляем ответ
        printf("Сервер: Отправляю ответ: %d\n", msg_data);
        server_to_transport!MSG_RESPONSE, msg_data;
    }
    :: else -> {
        printf("Сервер: Неожиданный тип сообщения: %d\n", msg_type);
    }
    fi;
}

// Инициализация системы
init {
    printf("=== Инициализация OPC UA системы ===\n");
    
    // Запускаем все процессы
    run OPCUAClient();
    run SecurityLayer();
    run TransportLayer();
    run OPCUAServer();
    
    printf("=== Все процессы запущены ===\n");
}

// LTL свойства для верификации

// Безопасность: аутентификация обязательна перед доступом
ltl auth_required { 
    [] (message_sent -> client_authenticated) 
}

// Безопасность: неавторизованные запросы не обрабатываются
ltl unauthorized_blocked { 
    [] (!client_authorized -> !message_received) 
}

// Безопасность: безопасный канал открыт перед передачей
ltl secure_channel_before_transmission { 
    [] (message_sent -> secure_channel_open) 
}

// Живость: авторизованные запросы обрабатываются
ltl authorized_processed { 
    [] (client_authorized && message_sent -> <> message_received) 
}

// Живость: ответы доставляются клиенту
ltl response_delivered { 
    [] (response_sent -> <> response_received) 
}

// Отсутствие тупиков в системе безопасности
ltl no_security_deadlock { 
    [] <> (client_authenticated || session_closed) 
}

// Корректность последовательности операций
ltl correct_sequence { 
    [] (message_sent -> (<> message_received && <> response_sent && <> response_received)) 
}

// Безопасность: сеанс установлен перед передачей данных
ltl session_before_data { 
    [] (message_sent -> session_established) 
}
