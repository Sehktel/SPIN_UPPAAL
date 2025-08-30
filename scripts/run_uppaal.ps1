# PowerShell скрипт для автоматизации работы с UPPAAL
# Автор: Образовательный проект SPIN vs UPPAAL
# Описание: Автоматизирует процесс верификации UPPAAL моделей

param(
    [string]$ModelPath = "..\models\uppaal\traffic_light.xml",
    [string]$QueriesPath = "..\models\uppaal\queries.xml",
    [string]$OutputDir = "..\results",
    [string]$UppaalPath = "",
    [switch]$Simulation,
    [switch]$Verification,
    [switch]$Help
)

# Функция для вывода справки
function Show-Help {
    Write-Host @"
Скрипт для автоматизации работы с UPPAAL

Использование:
    .\run_uppaal.ps1 [параметры]

Параметры:
    -ModelPath <путь>     Путь к модели UPPAAL (по умолчанию: ../models/uppaal/traffic_light.xml)
    -QueriesPath <путь>   Путь к файлу запросов (по умолчанию: ../models/uppaal/queries.xml)
    -OutputDir <путь>     Директория для результатов (по умолчанию: ../results)
    -UppaalPath <путь>    Путь к исполняемому файлу UPPAAL
    -Simulation           Запуск симуляции модели
    -Verification         Запуск верификации модели
    -Help                 Показать эту справку

Примеры:
    .\run_uppaal.ps1 -Simulation
    .\run_uppaal.ps1 -Verification -UppaalPath "C:\UPPAAL\uppaal.jar"
    .\run_uppaal.ps1 -Help

"@
}

# Функция для поиска UPPAAL
function Find-UppaalInstallation {
    if ($UppaalPath -and (Test-Path $UppaalPath)) {
        Write-Host "✓ UPPAAL найден по указанному пути: $UppaalPath" -ForegroundColor Green
        return $UppaalPath
    }
    
    # Поиск в стандартных местах
    $possiblePaths = @(
        "C:\Program Files\UPPAAL\uppaal.jar",
        "C:\UPPAAL\uppaal.jar",
        "$env:USERPROFILE\UPPAAL\uppaal.jar",
        "$env:USERPROFILE\Desktop\UPPAAL\uppaal.jar"
    )
    
    foreach ($path in $possiblePaths) {
        if (Test-Path $path) {
            Write-Host "✓ UPPAAL найден: $path" -ForegroundColor Green
            return $path
        }
    }
    
    # Поиск в PATH
    try {
        $uppaalVersion = uppaal --version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ UPPAAL найден в PATH: $uppaalVersion" -ForegroundColor Green
            return "uppaal"
        }
    }
    catch {
        # Продолжаем поиск
    }
    
    Write-Host "✗ UPPAAL не найден" -ForegroundColor Red
    Write-Host "Пожалуйста, установите UPPAAL с https://uppaal.org/download/" -ForegroundColor Yellow
    return $null
}

# Функция для проверки Java
function Test-JavaInstallation {
    try {
        $javaVersion = java -version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ Java найден: $($javaVersion[0])" -ForegroundColor Green
            return $true
        }
    }
    catch {
        Write-Host "✗ Java не найден" -ForegroundColor Red
        Write-Host "Пожалуйста, установите Java Runtime Environment (JRE)" -ForegroundColor Yellow
        return $false
    }
    return $false
}

# Функция для создания директории результатов
function Initialize-OutputDirectory {
    if (!(Test-Path $OutputDir)) {
        New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
        Write-Host "✓ Создана директория результатов: $OutputDir" -ForegroundColor Green
    }
}

# Функция для проверки модели
function Test-ModelSyntax {
    Write-Host "`n1. Проверка синтаксиса модели..." -ForegroundColor Yellow
    
    if (!(Test-Path $ModelPath)) {
        Write-Host "✗ Модель не найдена: $ModelPath" -ForegroundColor Red
        return $false
    }
    
    # Простая проверка XML синтаксиса
    try {
        [xml]$model = Get-Content $ModelPath
        Write-Host "✓ XML синтаксис корректен" -ForegroundColor Green
        return $true
    }
    catch {
        Write-Host "✗ Ошибка XML синтаксиса: $($_.Exception.Message)" -ForegroundColor Red
        return $false
    }
}

# Функция для проверки запросов
function Test-QueriesSyntax {
    Write-Host "`n2. Проверка синтаксиса запросов..." -ForegroundColor Yellow
    
    if (!(Test-Path $QueriesPath)) {
        Write-Host "✗ Файл запросов не найден: $QueriesPath" -ForegroundColor Red
        return $false
    }
    
    # Простая проверка XML синтаксиса
    try {
        [xml]$queries = Get-Content $QueriesPath
        Write-Host "✓ XML синтаксис запросов корректен" -ForegroundColor Green
        return $true
    }
    catch {
        Write-Host "✗ Ошибка XML синтаксиса запросов: $($_.Exception.Message)" -ForegroundColor Red
        return $false
    }
}

# Функция для симуляции модели
function Invoke-Simulation {
    Write-Host "`n=== ЗАПУСК СИМУЛЯЦИИ UPPAAL ===" -ForegroundColor Cyan
    
    $outputFile = Join-Path $OutputDir "uppaal_simulation_results.txt"
    
    Write-Host "Симуляция модели: $ModelPath"
    Write-Host "Результаты будут сохранены в: $outputFile"
    
    if (!(Test-ModelSyntax)) {
        return
    }
    
    # Создание скрипта симуляции
    $simulationScript = @"
// Скрипт симуляции UPPAAL
// Автоматически сгенерирован

// Загрузка модели
load "$ModelPath"

// Настройка симуляции
set simulation_time 1000
set simulation_steps 100

// Запуск симуляции
simulate

// Сохранение результатов
save_simulation_results "$outputFile"

// Завершение
exit
"@
    
    $scriptPath = Join-Path $OutputDir "simulation_script.txt"
    $simulationScript | Out-File -FilePath $scriptPath -Encoding UTF8
    
    Write-Host "✓ Скрипт симуляции создан: $scriptPath" -ForegroundColor Green
    Write-Host "ℹ Для запуска симуляции используйте UPPAAL GUI и загрузите скрипт" -ForegroundColor Yellow
}

# Функция для верификации модели
function Invoke-Verification {
    Write-Host "`n=== ЗАПУСК ВЕРИФИКАЦИИ UPPAAL ===" -ForegroundColor Cyan
    
    $outputFile = Join-Path $OutputDir "uppaal_verification_results.txt"
    
    Write-Host "Верификация модели: $ModelPath"
    Write-Host "Файл запросов: $QueriesPath"
    Write-Host "Результаты будут сохранены в: $outputFile"
    
    if (!(Test-ModelSyntax) -or !(Test-QueriesSyntax)) {
        return
    }
    
    # Создание скрипта верификации
    $verificationScript = @"
// Скрипт верификации UPPAAL
// Автоматически сгенерирован

// Загрузка модели
load "$ModelPath"

// Загрузка запросов
load_queries "$QueriesPath"

// Настройка верификации
set verification_timeout 300
set verification_memory 2048

// Запуск верификации всех запросов
verify_all_queries

// Сохранение результатов
save_verification_results "$outputFile"

// Завершение
exit
"@
    
    $scriptPath = Join-Path $OutputDir "verification_script.txt"
    $verificationScript | Out-File -FilePath $scriptPath -Encoding UTF8
    
    Write-Host "✓ Скрипт верификации создан: $scriptPath" -ForegroundColor Green
    Write-Host "ℹ Для запуска верификации используйте UPPAAL GUI и загрузите скрипт" -ForegroundColor Yellow
}

# Функция для создания отчета
function Generate-Report {
    Write-Host "`n=== ГЕНЕРАЦИЯ ОТЧЕТА ===" -ForegroundColor Cyan
    
    $reportFile = Join-Path $OutputDir "uppaal_report.md"
    
    $report = @"
# Отчет по верификации UPPAAL

## Информация о модели
- **Модель**: $ModelPath
- **Запросы**: $QueriesPath
- **Дата**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

## Результаты проверки синтаксиса
- **Модель**: $(if (Test-ModelSyntax) { "✓ Корректна" } else { "✗ Ошибки" })
- **Запросы**: $(if (Test-QueriesSyntax) { "✓ Корректны" } else { "✗ Ошибки" })

## Инструкции по использованию

### Симуляция
1. Откройте UPPAAL
2. Загрузите модель: $ModelPath
3. Запустите симуляцию через меню Simulation
4. Результаты будут сохранены в: $(Join-Path $OutputDir "uppaal_simulation_results.txt")

### Верификация
1. Откройте UPPAAL
2. Загрузите модель: $ModelPath
3. Загрузите запросы: $QueriesPath
4. Запустите верификацию через меню Verification
5. Результаты будут сохранены в: $(Join-Path $OutputDir "uppaal_verification_results.txt")

## Структура модели
Модель включает следующие компоненты:
- **TrafficLight**: Основной контроллер светофора
- **Pedestrian**: Процесс пешехода
- **Car**: Процесс автомобиля
- **EmergencyService**: Служба экстренной помощи
- **SystemMonitor**: Мониторинг системы

## Временные ограничения
- Красный свет: 30 единиц времени
- Желтый свет: 5 единиц времени
- Зеленый свет: 45 единиц времени
- Время перехода пешехода: 15 единиц времени
- Время проезда автомобиля: 8 единиц времени

## Свойства для верификации
Модель проверяет следующие свойства:
1. **Безопасность**: Отсутствие конфликтов
2. **Живость**: Доступность ресурсов
3. **Временные ограничения**: Корректность таймеров
4. **Отсутствие deadlock'ов**: Прогресс системы
5. **Справедливость**: Равномерное распределение ресурсов

## Примечания
- Для корректной работы требуется UPPAAL 4.1 или выше
- Рекомендуется использовать GUI интерфейс для анализа результатов
- При больших моделях может потребоваться увеличение лимитов памяти
"@
    
    $report | Out-File -FilePath $reportFile -Encoding UTF8
    Write-Host "✓ Отчет создан: $reportFile" -ForegroundColor Green
}

# Основная логика скрипта
function Main {
    Write-Host "=== UPPAAL АВТОМАТИЗАЦИЯ ВЕРИФИКАЦИИ ===" -ForegroundColor Magenta
    Write-Host "Версия: 1.0" -ForegroundColor Gray
    Write-Host "Автор: Образовательный проект SPIN vs UPPAAL" -ForegroundColor Gray
    
    # Проверка параметра справки
    if ($Help) {
        Show-Help
        return
    }
    
    # Проверка зависимостей
    Write-Host "`nПроверка зависимостей..." -ForegroundColor Yellow
    if (!(Find-UppaalInstallation)) {
        Write-Host "✗ UPPAAL не найден. Завершение работы." -ForegroundColor Red
        return
    }
    
    if (!(Test-JavaInstallation)) {
        Write-Host "✗ Java не найден. Завершение работы." -ForegroundColor Red
        return
    }
    
    # Инициализация директории результатов
    Initialize-OutputDirectory
    
    # Проверка файлов
    if (!(Test-Path $ModelPath)) {
        Write-Host "✗ Модель не найдена: $ModelPath" -ForegroundColor Red
        return
    }
    
    if (!(Test-Path $QueriesPath)) {
        Write-Host "✗ Файл запросов не найден: $QueriesPath" -ForegroundColor Red
        return
    }
    
    # Запуск операций
    if ($Simulation) {
        Invoke-Simulation
    }
    
    if ($Verification) {
        Invoke-Verification
    }
    
    # Если не указаны конкретные операции, запускаем обе
    if (!$Simulation -and !$Verification) {
        Invoke-Simulation
        Invoke-Verification
    }
    
    # Генерация отчета
    Generate-Report
    
    Write-Host "`n=== ОБРАБОТКА ЗАВЕРШЕНА ===" -ForegroundColor Magenta
    Write-Host "Результаты сохранены в: $OutputDir" -ForegroundColor Green
    Write-Host "ℹ Для запуска симуляции/верификации используйте UPPAAL GUI" -ForegroundColor Yellow
}

# Запуск основной функции
Main
