// BANDERA модель светофора на Java
// BANDERA - специализированный инструмент для верификации Java программ
// Демонстрирует абстракцию и специализацию на Java

import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Модель светофора для верификации в BANDERA
 * Использует атомарные операции для обеспечения потокобезопасности
 */
public class TrafficLight {
    
    // Состояния светофора
    public enum LightState {
        RED, YELLOW, GREEN
    }
    
    // Переменные состояния
    private LightState lightState;
    private AtomicInteger carsWaiting;
    private AtomicBoolean pedestrianWaiting;
    private AtomicInteger timer;
    private int timerLimit;
    
    // Константы
    private static final int MAX_CARS = 10;
    private static final int RED_TIMER = 5;
    private static final int YELLOW_TIMER = 3;
    private static final int GREEN_TIMER = 8;
    
    /**
     * Конструктор
     */
    public TrafficLight() {
        this.lightState = LightState.RED;
        this.carsWaiting = new AtomicInteger(0);
        this.pedestrianWaiting = new AtomicBoolean(false);
        this.timer = new AtomicInteger(0);
        this.timerLimit = 0;
    }
    
    /**
     * Запуск таймера
     * @param limit лимит таймера
     */
    public void startTimer(int limit) {
        if (limit > 0) {
            this.timerLimit = limit;
            this.timer.set(0);
        }
    }
    
    /**
     * Увеличение счетчика таймера
     */
    public void tick() {
        if (timer.get() < timerLimit) {
            timer.incrementAndGet();
        }
    }
    
    /**
     * Сброс таймера
     */
    public void resetTimer() {
        this.timer.set(0);
        this.timerLimit = 0;
    }
    
    /**
     * Переход на желтый свет
     */
    public void toYellow() {
        if (lightState == LightState.RED && 
            (carsWaiting.get() > 0 || pedestrianWaiting.get())) {
            lightState = LightState.YELLOW;
            startTimer(YELLOW_TIMER);
        }
    }
    
    /**
     * Переход на зеленый свет
     */
    public void toGreen() {
        if (lightState == LightState.YELLOW && 
            timer.get() >= timerLimit) {
            lightState = LightState.GREEN;
            startTimer(GREEN_TIMER);
        }
    }
    
    /**
     * Переход на красный свет
     */
    public void toRed() {
        if (lightState == LightState.GREEN && 
            timer.get() >= timerLimit) {
            lightState = LightState.RED;
            resetTimer();
            
            // Машина проехала
            if (carsWaiting.get() > 0) {
                carsWaiting.decrementAndGet();
            }
            
            // Пешеход перешел
            pedestrianWaiting.set(false);
        }
    }
    
    /**
     * Прибытие машины
     */
    public void carArrive() {
        if (carsWaiting.get() < MAX_CARS) {
            carsWaiting.incrementAndGet();
        }
    }
    
    /**
     * Прибытие пешехода
     */
    public void pedestrianArrive() {
        if (!pedestrianWaiting.get()) {
            pedestrianWaiting.set(true);
        }
    }
    
    /**
     * Получение текущего состояния светофора
     * @return текущее состояние
     */
    public LightState getLightState() {
        return lightState;
    }
    
    /**
     * Получение количества ожидающих машин
     * @return количество машин
     */
    public int getCarsWaiting() {
        return carsWaiting.get();
    }
    
    /**
     * Проверка, ждет ли пешеход
     * @return true если пешеход ждет
     */
    public boolean isPedestrianWaiting() {
        return pedestrianWaiting.get();
    }
    
    /**
     * Получение текущего значения таймера
     * @return значение таймера
     */
    public int getTimer() {
        return timer.get();
    }
    
    /**
     * Получение лимита таймера
     * @return лимит таймера
     */
    public int getTimerLimit() {
        return timerLimit;
    }
    
    /**
     * Проверка инвариантов безопасности
     * @return true если все инварианты выполняются
     */
    public boolean checkInvariants() {
        // Инвариант 1: Светофор всегда должен быть в одном из трех состояний
        if (lightState != LightState.RED && 
            lightState != LightState.YELLOW && 
            lightState != LightState.GREEN) {
            return false;
        }
        
        // Инвариант 2: Количество машин должно быть в допустимых пределах
        if (carsWaiting.get() < 0 || carsWaiting.get() > MAX_CARS) {
            return false;
        }
        
        // Инвариант 3: Таймер должен быть в корректном состоянии
        if (timer.get() < 0 || timer.get() > timerLimit) {
            return false;
        }
        
        // Инвариант 4: Не должно быть зеленого света при ожидающем пешеходе
        if (lightState == LightState.GREEN && pedestrianWaiting.get()) {
            return false;
        }
        
        return true;
    }
    
    /**
     * Основной метод для демонстрации
     */
    public static void main(String[] args) {
        TrafficLight trafficLight = new TrafficLight();
        
        // Проверка начального состояния
        assert trafficLight.getLightState() == LightState.RED;
        assert trafficLight.getCarsWaiting() == 0;
        assert !trafficLight.isPedestrianWaiting();
        assert trafficLight.checkInvariants();
        
        // Симуляция работы
        trafficLight.carArrive();
        trafficLight.toYellow();
        
        // Проверка после изменения
        assert trafficLight.getLightState() == LightState.YELLOW;
        assert trafficLight.getCarsWaiting() == 1;
        assert trafficLight.checkInvariants();
    }
}
