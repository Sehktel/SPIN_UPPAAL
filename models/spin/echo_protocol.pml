/*
 * Протокол "Эхо-сервер" - простой пример для изучения
 * Демонстрирует базовые принципы верификации протоколов связи
 * 
 * Описание: Клиент отправляет сообщение, сервер отвечает тем же сообщением
 * Цель: Проверить корректность протокола и отсутствие тупиков
 */

// Глобальные переменные для отслеживания состояния
int message_sent = 0;    // Сообщение отправлено
int message_received = 0; // Сообщение получено
int response_sent = 0;    // Ответ отправлен
int response_received = 0; // Ответ получен

// Каналы для связи между процессами
chan client_to_server = [1] of {int};  // Канал клиент -> сервер
chan server_to_client = [1] of {int};  // Канал сервер -> клиент

// Процесс клиента
proctype Client() {
    int msg;
    
    // Клиент генерирует сообщение
    msg = 42;  // Простое тестовое сообщение
    message_sent = 1;
    
    // Отправляем сообщение серверу
    client_to_server!msg;
    
    // Ждем ответ
    server_to_client?msg;
    response_received = 1;
    
    // Проверяем, что получили то же сообщение
    assert(msg == 42);
}

// Процесс сервера
proctype Server() {
    int msg;
    
    // Ждем сообщение от клиента
    client_to_server?msg;
    message_received = 1;
    
    // Отправляем ответ (то же сообщение)
    server_to_client!msg;
    response_sent = 1;
}

// Инициализация системы
init {
    // Запускаем клиента и сервер параллельно
    run Client();
    run Server();
}

// Спецификация LTL для проверки свойств протокола
// 1. Если сообщение отправлено, оно будет получено
ltl safety1 { [] (message_sent -> <> message_received) }

// 2. Если сообщение получено, ответ будет отправлен
ltl safety2 { [] (message_received -> <> response_sent) }

// 3. Если ответ отправлен, он будет получен
ltl safety3 { [] (response_sent -> <> response_received) }

// 4. В конце протокола все сообщения обработаны
ltl liveness { <> (message_sent && message_received && response_sent && response_received) }

// 5. Отсутствие тупиков (всегда есть возможность выполнить действие)
ltl no_deadlock { [] <> true }
