---------------------------- MODULE DistributedControl ----------------------------
-- TLA+ модель распределенной системы управления
-- Демонстрирует возможности TLA+ для сложных распределенных протоколов
-- Автор: Senior Developer
-- Дата: 2024-12-19
--
-- Проблема: SPIN/UPPAAL не могут эффективно моделировать сложные распределенные системы
-- Решение: TLA+ специализирован для распределенных систем и временной логики

EXTENDS Naturals, Sequences, FiniteSets

-- Константы системы
CONSTANTS
  NodeCount,    -- Количество узлов в системе
  MaxMessages,  -- Максимальное количество сообщений
  Timeout       -- Таймаут для операций

-- Переменные состояния
VARIABLES
  nodes,        -- Состояния узлов
  messages,     -- Очередь сообщений
  global_state, -- Глобальное состояние системы
  time          -- Время системы

-- Определение типов
NodeState == [state: {"IDLE", "ACTIVE", "PROCESSING", "ERROR", "RECOVERING"},
              id: 1..NodeCount,
              last_heartbeat: 0..Timeout,
              message_count: 0..MaxMessages]

Message == [from: 1..NodeCount,
            to: 1..NodeCount,
            type: {"HEARTBEAT", "DATA", "CONTROL", "ERROR"},
            data: STRING,
            timestamp: 0..Timeout]

GlobalState == [active_nodes: SUBSET (1..NodeCount),
                total_messages: 0..MaxMessages,
                system_health: {"HEALTHY", "DEGRADED", "CRITICAL"},
                last_update: 0..Timeout]

-- Инициализация
Init ==
  /\ nodes = [i \in 1..NodeCount |-> [state |-> "IDLE",
                                       id |-> i,
                                       last_heartbeat |-> 0,
                                       message_count |-> 0]]
  /\ messages = <<>>
  /\ global_state = [active_nodes |-> {},
                     total_messages |-> 0,
                     system_health |-> "HEALTHY",
                     last_update |-> 0]
  /\ time = 0

-- Действия узлов
NodeActivate(i) ==
  /\ i \in 1..NodeCount
  /\ nodes[i].state = "IDLE"
  /\ nodes' = [nodes EXCEPT ![i] = [nodes[i] EXCEPT !.state = "ACTIVE",
                                                           !.last_heartbeat = time]]
  /\ global_state' = [global_state EXCEPT !.active_nodes = global_state.active_nodes \cup {i}]
  /\ UNCHANGED <<messages, time>>

NodeProcess(i) ==
  /\ i \in 1..NodeCount
  /\ nodes[i].state = "ACTIVE"
  /\ nodes[i].message_count < MaxMessages
  /\ nodes' = [nodes EXCEPT ![i] = [nodes[i] EXCEPT !.state = "PROCESSING",
                                                           !.message_count = nodes[i].message_count + 1]]
  /\ UNCHANGED <<messages, global_state, time>>

NodeComplete(i) ==
  /\ i \in 1..NodeCount
  /\ nodes[i].state = "PROCESSING"
  /\ nodes' = [nodes EXCEPT ![i] = [nodes[i] EXCEPT !.state = "ACTIVE"]]
  /\ UNCHANGED <<messages, global_state, time>>

NodeError(i) ==
  /\ i \in 1..NodeCount
  /\ nodes[i].state \in {"ACTIVE", "PROCESSING"}
  /\ nodes' = [nodes EXCEPT ![i] = [nodes[i] EXCEPT !.state = "ERROR"]]
  /\ global_state' = [global_state EXCEPT !.active_nodes = global_state.active_nodes \ {i}]
  /\ UNCHANGED <<messages, time>>

NodeRecover(i) ==
  /\ i \in 1..NodeCount
  /\ nodes[i].state = "ERROR"
  /\ nodes' = [nodes EXCEPT ![i] = [nodes[i] EXCEPT !.state = "IDLE",
                                                           !.message_count = 0]]
  /\ UNCHANGED <<messages, global_state, time>>

-- Действия с сообщениями
SendMessage(from, to, msg_type, msg_data) ==
  /\ from \in 1..NodeCount
  /\ to \in 1..NodeCount
  /\ from /= to
  /\ nodes[from].state = "ACTIVE"
  /\ nodes[to].state = "ACTIVE"
  /\ Len(messages) < MaxMessages
  /\ messages' = messages \o <<[from |-> from,
                               to |-> to,
                               type |-> msg_type,
                               data |-> msg_data,
                               timestamp |-> time]>>
  /\ global_state' = [global_state EXCEPT !.total_messages = global_state.total_messages + 1]
  /\ UNCHANGED <<nodes, time>>

ProcessMessage(i) ==
  /\ i \in 1..NodeCount
  /\ nodes[i].state = "ACTIVE"
  /\ \E msg \in messages:
       msg.to = i /\ msg.timestamp + 10 >= time
  /\ LET msg == CHOOSE m \in messages: m.to = i /\ m.timestamp + 10 >= time
     IN
     /\ messages' = [m \in messages: m /= msg]
     /\ global_state' = [global_state EXCEPT !.total_messages = global_state.total_messages - 1]
     /\ UNCHANGED <<nodes, time>>

-- Временные действия
TimeAdvance ==
  /\ time < Timeout
  /\ time' = time + 1
  /\ UNCHANGED <<nodes, messages, global_state>>

-- Обновление глобального состояния
UpdateGlobalState ==
  /\ LET active_count == Cardinality(global_state.active_nodes)
         total_msg == global_state.total_messages
     IN
     /\ global_state' = [global_state EXCEPT !.system_health = 
                          IF active_count = 0 THEN "CRITICAL"
                          ELSE IF active_count < NodeCount/2 THEN "DEGRADED"
                          ELSE "HEALTHY",
                        !.last_update = time]
  /\ UNCHANGED <<nodes, messages, time>>

-- Следующее состояние
Next ==
  \/ \E i \in 1..NodeCount: NodeActivate(i)
  \/ \E i \in 1..NodeCount: NodeProcess(i)
  \/ \E i \in 1..NodeCount: NodeComplete(i)
  \/ \E i \in 1..NodeCount: NodeError(i)
  \/ \E i \in 1..NodeCount: NodeRecover(i)
  \/ \E i, j \in 1..NodeCount, t \in {"HEARTBEAT", "DATA", "CONTROL", "ERROR"}, d \in STRING:
       SendMessage(i, j, t, d)
  \/ \E i \in 1..NodeCount: ProcessMessage(i)
  \/ TimeAdvance
  \/ UpdateGlobalState

-- Инварианты безопасности
TypeOK ==
  /\ nodes \in [1..NodeCount -> NodeState]
  /\ messages \in Seq(Message)
  /\ global_state \in GlobalState
  /\ time \in 0..Timeout

NodeStateInvariant ==
  \A i \in 1..NodeCount:
    /\ nodes[i].id = i
    /\ nodes[i].last_heartbeat \in 0..Timeout
    /\ nodes[i].message_count \in 0..MaxMessages

MessageInvariant ==
  \A msg \in messages:
    /\ msg.from \in 1..NodeCount
    /\ msg.to \in 1..NodeCount
    /\ msg.from /= msg.to
    /\ msg.timestamp \in 0..Timeout

GlobalStateInvariant ==
  /\ global_state.active_nodes \subseteq (1..NodeCount)
  /\ global_state.total_messages \in 0..MaxMessages
  /\ global_state.last_update \in 0..Timeout

-- Liveness свойства
NodeEventuallyActive ==
  \A i \in 1..NodeCount:
    WF_<<nodes, global_state>>(NodeActivate(i))

MessageEventuallyProcessed ==
  \A msg \in messages:
    WF_<<messages, global_state>>(ProcessMessage(CHOOSE i \in 1..NodeCount: i = msg.to))

SystemEventuallyHealthy ==
  WF_<<global_state>>(UpdateGlobalState)

-- Спецификация
Spec ==
  Init /\ [][Next]_<<nodes, messages, global_state, time>>
  /\ NodeEventuallyActive
  /\ MessageEventuallyProcessed
  /\ SystemEventuallyHealthy

-- Теоремы для проверки
THEOREM Spec => []TypeOK
THEOREM Spec => []NodeStateInvariant
THEOREM Spec => []MessageInvariant
THEOREM Spec => []GlobalStateInvariant

=============================================================================

