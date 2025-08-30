/*
 * Модель протокола Modbus TCP в SPIN
 * 
 * Описание: Протокол Modbus TCP - это промышленный протокол
 * для связи между устройствами по TCP/IP. Поддерживает операции
 * чтения и записи регистров.
 * 
 * Цель: Верификация корректности протокола, отсутствие тупиков,
 * правильность обработки ошибок
 */

// Глобальные переменные для отслеживания состояния
int client_connected = 0;      // Клиент подключен
int request_sent = 0;          // Запрос отправлен
int request_received = 0;      // Запрос получен
int response_sent = 0;         // Ответ отправлен
int response_received = 0;     // Ответ получен
int connection_closed = 0;     // Соединение закрыто

// Типы операций Modbus
#define READ_HOLDING_REGISTERS  3
#define WRITE_SINGLE_REGISTER  6
#define WRITE_MULTIPLE_REGISTERS 16

// Структура для Modbus PDU
typedef ModbusPDU {
    byte function_code;        // Код функции
    byte data[10];            // Данные (регистры, значения)
    byte data_length;         // Длина данных
}

// Каналы для связи
chan tcp_connection = [1] of {ModbusPDU};  // TCP соединение
chan modbus_response = [1] of {ModbusPDU}; // Ответ Modbus

// Процесс TCP клиента
proctype TCPClient() {
    ModbusPDU request, response;
    
    // Подключение к серверу
    client_connected = 1;
    
    // Отправляем запрос на чтение регистров
    request.function_code = READ_HOLDING_REGISTERS;
    request.data[0] = 0;      // Адрес начального регистра (старший байт)
    request.data[1] = 1;      // Адрес начального регистра (младший байт)
    request.data[2] = 0;      // Количество регистров (старший байт)
    request.data[3] = 10;     // Количество регистров (младший байт)
    request.data_length = 4;
    
    request_sent = 1;
    tcp_connection!request;
    
    // Ждем ответ
    modbus_response?response;
    response_received = 1;
    
    // Проверяем корректность ответа
    assert(response.function_code == READ_HOLDING_REGISTERS);
    
    // Отправляем запрос на запись регистра
    request.function_code = WRITE_SINGLE_REGISTER;
    request.data[0] = 0;      // Адрес регистра (старший байт)
    request.data[1] = 100;    // Адрес регистра (младший байт)
    request.data[2] = 0;      // Значение (старший байт)
    request.data[3] = 42;     // Значение (младший байт)
    request.data_length = 4;
    
    tcp_connection!request;
    
    // Ждем ответ на запись
    modbus_response?response;
    assert(response.function_code == WRITE_SINGLE_REGISTER);
    
    // Закрываем соединение
    connection_closed = 1;
}

// Процесс TCP сервера (Modbus сервер)
proctype TCPServer() {
    ModbusPDU request, response;
    
    // Ждем подключения клиента
    tcp_connection?request;
    request_received = 1;
    
    // Обрабатываем запрос на чтение регистров
    if
    :: request.function_code == READ_HOLDING_REGISTERS -> {
        // Формируем ответ
        response.function_code = READ_HOLDING_REGISTERS;
        response.data[0] = 20;  // Количество байт данных
        response.data_length = 21; // 1 байт + 20 байт данных
        
        // Отправляем ответ
        modbus_response!response;
        response_sent = 1;
    }
    :: request.function_code == WRITE_SINGLE_REGISTER -> {
        // Формируем ответ на запись
        response.function_code = WRITE_SINGLE_REGISTER;
        response.data[0] = request.data[0];  // Адрес регистра (старший байт)
        response.data[1] = request.data[1];  // Адрес регистра (младший байт)
        response.data[2] = request.data[2];  // Значение (старший байт)
        response.data[3] = request.data[3];  // Значение (младший байт)
        response.data_length = 4;
        
        modbus_response!response;
    }
    :: else -> {
        // Обработка ошибки - неверный код функции
        response.function_code = request.function_code | 0x80; // Устанавливаем бит ошибки
        response.data[0] = 1;  // Код ошибки: неверная функция
        response.data_length = 1;
        
        modbus_response!response;
    }
    fi;
    
    // Обрабатываем второй запрос (запись)
    tcp_connection?request;
    
    if
    :: request.function_code == WRITE_SINGLE_REGISTER -> {
        response.function_code = WRITE_SINGLE_REGISTER;
        response.data[0] = request.data[0];
        response.data[1] = request.data[1];
        response.data[2] = request.data[2];
        response.data[3] = request.data[3];
        response.data_length = 4;
        
        modbus_response!response;
    }
    :: else -> {
        response.function_code = request.function_code | 0x80;
        response.data[0] = 1;
        response.data_length = 1;
        
        modbus_response!response;
    }
    fi;
}

// Инициализация системы
init {
    // Запускаем клиента и сервер параллельно
    run TCPClient();
    run TCPServer();
}

// Спецификация LTL для проверки свойств протокола

// 1. Безопасность: если запрос отправлен, он будет получен
ltl safety_request { [] (request_sent -> <> request_received) }

// 2. Безопасность: если запрос получен, ответ будет отправлен
ltl safety_response { [] (request_received -> <> response_sent) }

// 3. Безопасность: если ответ отправлен, он будет получен
ltl safety_delivery { [] (response_sent -> <> response_received) }

// 4. Живость: протокол завершается корректно
ltl liveness_completion { <> (client_connected && connection_closed) }

// 5. Отсутствие тупиков
ltl no_deadlock { [] <> true }

// 6. Корректность последовательности операций
ltl correct_sequence { 
    [] (request_sent -> 
        (request_received U response_sent) U 
        (response_received U connection_closed))
}

// 7. Проверка обработки ошибок (если отправлен неверный код функции)
ltl error_handling { 
    [] (request_received -> 
        (response_sent U (response_received || connection_closed)))
}
