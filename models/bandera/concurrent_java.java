// BANDERA модель конкурентной Java системы
// Автор: Senior Developer
// Описание: Модель системы с несколькими потоками, синхронизацией и управлением ресурсами

import java.util.concurrent.*;
import java.util.concurrent.locks.*;
import java.util.concurrent.atomic.*;

public class ConcurrentJavaSystem {
    
    // Состояния системы
    public enum SystemState {
        INITIALIZING, OPERATIONAL, EMERGENCY, SHUTDOWN, MAINTENANCE
    }
    
    public enum PumpState {
        STOPPED, STARTING, RUNNING, STOPPING, ERROR, MAINTENANCE
    }
    
    public enum ValveState {
        CLOSED, OPENING, OPEN, CLOSING, ERROR, MAINTENANCE
    }
    
    // Атомарные переменные для состояния системы
    private final AtomicReference<SystemState> systemState = 
        new AtomicReference<>(SystemState.INITIALIZING);
    
    private final AtomicReference<PumpState> pump1State = 
        new AtomicReference<>(PumpState.STOPPED);
    
    private final AtomicReference<PumpState> pump2State = 
        new AtomicReference<>(PumpState.STOPPED);
    
    private final AtomicReference<ValveState> valve1State = 
        new AtomicReference<>(ValveState.CLOSED);
    
    private final AtomicReference<ValveState> valve2State = 
        new AtomicReference<>(ValveState.CLOSED);
    
    // Счетчики и метрики
    private final AtomicInteger systemHealth = new AtomicInteger(100);
    private final AtomicInteger errorCount = new AtomicInteger(0);
    private final AtomicInteger activeAlarms = new AtomicInteger(0);
    private final AtomicInteger pendingTasks = new AtomicInteger(0);
    
    // Датчики
    private final AtomicInteger tank1Level = new AtomicInteger(500);
    private final AtomicInteger tank2Level = new AtomicInteger(300);
    private final AtomicInteger pump1Pressure = new AtomicInteger(0);
    private final AtomicInteger pump2Pressure = new AtomicInteger(0);
    
    // Блокировки для синхронизации
    private final ReentrantReadWriteLock systemLock = new ReentrantReadWriteLock();
    private final ReentrantLock pumpLock = new ReentrantLock();
    private final ReentrantLock valveLock = new ReentrantLock();
    
    // Условные переменные
    private final Condition pumpCondition = pumpLock.newCondition();
    private final Condition valveCondition = valveLock.newCondition();
    
    // Семафоры для ограничения доступа
    private final Semaphore pumpSemaphore = new Semaphore(1, true);
    private final Semaphore valveSemaphore = new Semaphore(2, true);
    
    // Пул потоков для выполнения задач
    private final ExecutorService taskExecutor = 
        Executors.newFixedThreadPool(4);
    
    // Очередь задач
    private final BlockingQueue<Runnable> taskQueue = 
        new LinkedBlockingQueue<>();
    
    // Флаг аварийной остановки
    private final AtomicBoolean emergencyActive = new AtomicBoolean(false);
    
    // Флаг режима обслуживания
    private final AtomicBoolean maintenanceMode = new AtomicBoolean(false);
    
    // Класс для управления насосом 1
    public class Pump1Controller implements Runnable {
        @Override
        public void run() {
            try {
                while (!Thread.currentThread().isInterrupted()) {
                    if (emergencyActive.get()) {
                        handleEmergency();
                        continue;
                    }
                    
                    if (maintenanceMode.get()) {
                        handleMaintenance();
                        continue;
                    }
                    
                    // Проверка состояния датчиков
                    if (!checkSensors()) {
                        handleSensorError();
                        continue;
                    }
                    
                    // Обработка команд управления
                    processPumpCommands();
                    
                    // Обновление состояния насоса
                    updatePumpState();
                    
                    Thread.sleep(100); // Задержка для симуляции
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        
        private void handleEmergency() {
            pumpLock.lock();
            try {
                pump1State.set(PumpState.STOPPING);
                pump1Pressure.set(0);
                systemHealth.addAndGet(-5);
            } finally {
                pumpLock.unlock();
            }
        }
        
        private void handleMaintenance() {
            pumpLock.lock();
            try {
                if (pump1State.get() == PumpState.RUNNING) {
                    pump1State.set(PumpState.STOPPING);
                    pump1Pressure.set(0);
                }
            } finally {
                pumpLock.unlock();
            }
        }
        
        private boolean checkSensors() {
            return tank1Level.get() > 100 && systemHealth.get() > 50;
        }
        
        private void handleSensorError() {
            errorCount.incrementAndGet();
            systemHealth.addAndGet(-10);
            activeAlarms.incrementAndGet();
        }
        
        private void processPumpCommands() {
            // Логика обработки команд управления насосом
            if (pump1State.get() == PumpState.STARTING) {
                pumpLock.lock();
                try {
                    pump1State.set(PumpState.RUNNING);
                    pendingTasks.incrementAndGet();
                } finally {
                    pumpLock.unlock();
                }
            }
        }
        
        private void updatePumpState() {
            if (pump1State.get() == PumpState.RUNNING) {
                pump1Pressure.addAndGet(5);
                tank1Level.addAndGet(-2);
            }
        }
    }
    
    // Класс для управления насосом 2
    public class Pump2Controller implements Runnable {
        @Override
        public void run() {
            try {
                while (!Thread.currentThread().isInterrupted()) {
                    if (emergencyActive.get()) {
                        handleEmergency();
                        continue;
                    }
                    
                    if (maintenanceMode.get()) {
                        handleMaintenance();
                        continue;
                    }
                    
                    // Проверка состояния датчиков
                    if (!checkSensors()) {
                        handleSensorError();
                        continue;
                    }
                    
                    // Обработка команд управления
                    processPumpCommands();
                    
                    // Обновление состояния насоса
                    updatePumpState();
                    
                    Thread.sleep(100); // Задержка для симуляции
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        
        private void handleEmergency() {
            pumpLock.lock();
            try {
                pump2State.set(PumpState.STOPPING);
                pump2Pressure.set(0);
                systemHealth.addAndGet(-5);
            } finally {
                pumpLock.unlock();
            }
        }
        
        private void handleMaintenance() {
            pumpLock.lock();
            try {
                if (pump2State.get() == PumpState.RUNNING) {
                    pump2State.set(PumpState.STOPPING);
                    pump2Pressure.set(0);
                }
            } finally {
                pumpLock.unlock();
            }
        }
        
        private boolean checkSensors() {
            return tank2Level.get() > 100 && systemHealth.get() > 50;
        }
        
        private void handleSensorError() {
            errorCount.incrementAndGet();
            systemHealth.addAndGet(-10);
            activeAlarms.incrementAndGet();
        }
        
        private void processPumpCommands() {
            // Логика обработки команд управления насосом
            if (pump2State.get() == PumpState.STARTING) {
                pumpLock.lock();
                try {
                    pump2State.set(PumpState.RUNNING);
                    pendingTasks.incrementAndGet();
                } finally {
                    pumpLock.unlock();
                }
            }
        }
        
        private void updatePumpState() {
            if (pump2State.get() == PumpState.RUNNING) {
                pump2Pressure.addAndGet(5);
                tank2Level.addAndGet(-1);
            }
        }
    }
    
    // Класс для управления клапанами
    public class ValveController implements Runnable {
        @Override
        public void run() {
            try {
                while (!Thread.currentThread().isInterrupted()) {
                    if (emergencyActive.get()) {
                        handleEmergency();
                        continue;
                    }
                    
                    if (maintenanceMode.get()) {
                        handleMaintenance();
                        continue;
                    }
                    
                    // Обработка команд управления клапанами
                    processValveCommands();
                    
                    // Обновление состояния клапанов
                    updateValveState();
                    
                    Thread.sleep(150); // Задержка для симуляции
                }
            } catch (InterruptedException e) {
                Thread.currentThread().isInterrupted();
            }
        }
        
        private void handleEmergency() {
            valveLock.lock();
            try {
                valve1State.set(ValveState.CLOSING);
                valve2State.set(ValveState.CLOSING);
            } finally {
                valveLock.unlock();
            }
        }
        
        private void handleMaintenance() {
            valveLock.lock();
            try {
                if (valve1State.get() == ValveState.OPEN) {
                    valve1State.set(ValveState.CLOSING);
                }
                if (valve2State.get() == ValveState.OPEN) {
                    valve2State.set(ValveState.CLOSING);
                }
            } finally {
                valveLock.unlock();
            }
        }
        
        private void processValveCommands() {
            // Логика обработки команд управления клапанами
            valveLock.lock();
            try {
                if (valve1State.get() == ValveState.OPENING) {
                    valve1State.set(ValveState.OPEN);
                    pendingTasks.incrementAndGet();
                }
                if (valve2State.get() == ValveState.OPENING) {
                    valve2State.set(ValveState.OPEN);
                    pendingTasks.incrementAndGet();
                }
            } finally {
                valveLock.unlock();
            }
        }
        
        private void updateValveState() {
            // Обновление состояния клапанов
            valveLock.lock();
            try {
                if (valve1State.get() == ValveState.CLOSING) {
                    valve1State.set(ValveState.CLOSED);
                    pendingTasks.decrementAndGet();
                }
                if (valve2State.get() == ValveState.CLOSING) {
                    valve2State.set(ValveState.CLOSED);
                    pendingTasks.decrementAndGet();
                }
            } finally {
                valveLock.unlock();
            }
        }
    }
    
    // Класс для системы безопасности
    public class SafetySystem implements Runnable {
        @Override
        public void run() {
            try {
                while (!Thread.currentThread().isInterrupted()) {
                    // Мониторинг безопасности
                    monitorSafety();
                    
                    // Обработка аварийных ситуаций
                    handleSafetyViolations();
                    
                    Thread.sleep(200); // Задержка для симуляции
                }
            } catch (InterruptedException e) {
                Thread.currentThread().isInterrupted();
            }
        }
        
        private void monitorSafety() {
            // Проверка критических параметров
            if (tank1Level.get() < 50 || tank2Level.get() < 30) {
                emergencyActive.set(true);
                systemState.set(SystemState.EMERGENCY);
                activeAlarms.incrementAndGet();
            }
            
            if (systemHealth.get() < 30) {
                emergencyActive.set(true);
                systemState.set(SystemState.EMERGENCY);
                activeAlarms.incrementAndGet();
            }
        }
        
        private void handleSafetyViolations() {
            if (emergencyActive.get()) {
                // Активация аварийной остановки
                systemLock.writeLock().lock();
                try {
                    systemState.set(SystemState.EMERGENCY);
                    // Остановка всех насосов и клапанов
                    pump1State.set(PumpState.STOPPING);
                    pump2State.set(PumpState.STOPPING);
                    valve1State.set(ValveState.CLOSING);
                    valve2State.set(ValveState.CLOSING);
                } finally {
                    systemLock.writeLock().unlock();
                }
            }
        }
    }
    
    // Методы управления системой
    public void startSystem() {
        systemLock.writeLock().lock();
        try {
            if (systemState.get() == SystemState.INITIALIZING) {
                systemState.set(SystemState.OPERATIONAL);
                
                // Запуск контроллеров
                taskExecutor.submit(new Pump1Controller());
                taskExecutor.submit(new Pump2Controller());
                taskExecutor.submit(new ValveController());
                taskExecutor.submit(new SafetySystem());
            }
        } finally {
            systemLock.writeLock().unlock();
        }
    }
    
    public void emergencyStop() {
        emergencyActive.set(true);
        systemState.set(SystemState.EMERGENCY);
        activeAlarms.incrementAndGet();
    }
    
    public void resetEmergency() {
        emergencyActive.set(false);
        systemState.set(SystemState.OPERATIONAL);
        activeAlarms.decrementAndGet();
    }
    
    public void enterMaintenance() {
        maintenanceMode.set(true);
        systemState.set(SystemState.MAINTENANCE);
    }
    
    public void exitMaintenance() {
        maintenanceMode.set(false);
        systemState.set(SystemState.OPERATIONAL);
    }
    
    public void shutdown() {
        systemState.set(SystemState.SHUTDOWN);
        taskExecutor.shutdown();
        try {
            if (!taskExecutor.awaitTermination(5, TimeUnit.SECONDS)) {
                taskExecutor.shutdownNow();
            }
        } catch (InterruptedException e) {
            taskExecutor.shutdownNow();
            Thread.currentThread().interrupt();
        }
    }
    
    // Геттеры для получения состояния системы
    public SystemState getSystemState() { return systemState.get(); }
    public PumpState getPump1State() { return pump1State.get(); }
    public PumpState getPump2State() { return pump2State.get(); }
    public ValveState getValve1State() { return valve1State.get(); }
    public ValveState getValve2State() { return valve2State.get(); }
    public int getSystemHealth() { return systemHealth.get(); }
    public int getErrorCount() { return errorCount.get(); }
    public int getActiveAlarms() { return activeAlarms.get(); }
    public int getPendingTasks() { return pendingTasks.get(); }
    public int getTank1Level() { return tank1Level.get(); }
    public int getTank2Level() { return tank2Level.get(); }
    public int getPump1Pressure() { return pump1Pressure.get(); }
    public int getPump2Pressure() { return pump2Pressure.get(); }
    public boolean isEmergencyActive() { return emergencyActive.get(); }
    public boolean isMaintenanceMode() { return maintenanceMode.get(); }
    
    // Метод для тестирования системы
    public static void main(String[] args) {
        ConcurrentJavaSystem system = new ConcurrentJavaSystem();
        
        try {
            // Запуск системы
            system.startSystem();
            
            // Симуляция работы системы
            Thread.sleep(5000);
            
            // Тестирование аварийной остановки
            system.emergencyStop();
            Thread.sleep(2000);
            
            // Сброс аварии
            system.resetEmergency();
            Thread.sleep(2000);
            
            // Переход в режим обслуживания
            system.enterMaintenance();
            Thread.sleep(2000);
            
            // Выход из режима обслуживания
            system.exitMaintenance();
            Thread.sleep(2000);
            
            // Завершение работы
            system.shutdown();
            
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            system.shutdown();
        }
    }
}
