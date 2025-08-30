#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Скрипт для верификации ПЛК моделей с использованием SPIN и UPPAAL
    
.DESCRIPTION
    Автоматизирует процесс верификации моделей ПЛК систем:
    - SPIN модели для логической верификации
    - UPPAAL модели для временной верификации
    - Генерация отчетов о соответствии требованиям безопасности
    
.PARAMETER Help
    Показать справку по использованию скрипта
    
.PARAMETER SpinModel
    Путь к SPIN модели для верификации
    
.PARAMETER UppaalModel
    Путь к UPPAAL модели для верификации
    
.PARAMETER UppaalQueries
    Путь к файлу TCTL запросов для UPPAAL
    
.PARAMETER OutputDir
    Директория для сохранения результатов верификации
    
.PARAMETER SafetyLevel
    Уровень безопасности для проверки (SIL1, SIL2, SIL3, SIL4)
    
.EXAMPLE
    .\run_plc_verification.ps1 -SpinModel "models/spin/plc_pump_system.pml" -UppaalModel "models/uppaal/plc_pump_system.xml"
    
.EXAMPLE
    .\run_plc_verification.ps1 -SafetyLevel SIL3 -OutputDir "results/plc_verification"
#>

param(
    [switch]$Help,
    [string]$SpinModel = "models/spin/plc_pump_system.pml",
    [string]$UppaalModel = "models/uppaal/plc_pump_system.xml",
    [string]$UppaalQueries = "models/uppaal/plc_pump_queries.xml",
    [string]$OutputDir = "results/plc_verification",
    [ValidateSet("SIL1", "SIL2", "SIL3", "SIL4")]
    [string]$SafetyLevel = "SIL2"
)

# Функция отображения справки
function Show-Help {
    Write-Host "=== ПЛК ВЕРИФИКАЦИЯ С ПОМОЩЬЮ SPIN И UPPAAL ===" -ForegroundColor Cyan
    Write-Host ""
    Write-Host "Использование:" -ForegroundColor Yellow
    Write-Host "  .\run_plc_verification.ps1 [параметры]"
    Write-Host ""
    Write-Host "Параметры:" -ForegroundColor Yellow
    Write-Host "  -Help              Показать эту справку"
    Write-Host "  -SpinModel         Путь к SPIN модели (по умолчанию: $SpinModel)"
    Write-Host "  -UppaalModel       Путь к UPPAAL модели (по умолчанию: $UppaalModel)"
    Write-Host "  -UppaalQueries     Путь к TCTL запросам (по умолчанию: $UppaalQueries)"
    Write-Host "  -OutputDir         Директория результатов (по умолчанию: $OutputDir)"
    Write-Host "  -SafetyLevel       Уровень безопасности SIL1-SIL4 (по умолчанию: $SafetyLevel)"
    Write-Host ""
    Write-Host "Примеры:" -ForegroundColor Yellow
    Write-Host "  .\run_plc_verification.ps1 -SafetyLevel SIL3"
    Write-Host "  .\run_plc_verification.ps1 -SpinModel 'models/spin/my_plc.pml'"
    Write-Host ""
}

# Функция проверки зависимостей
function Test-Dependencies {
    Write-Host "Проверка зависимостей..." -ForegroundColor Green
    
    # Проверка SPIN
    try {
        $spinVersion = spin -V 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ SPIN найден: $spinVersion" -ForegroundColor Green
        } else {
            Write-Host "✗ SPIN не найден или не работает" -ForegroundColor Red
            return $false
        }
    } catch {
        Write-Host "✗ SPIN не найден в PATH" -ForegroundColor Red
        return $false
    }
    
    # Проверка компилятора C
    try {
        $compiler = Get-Command gcc -ErrorAction SilentlyContinue
        if ($compiler) {
            Write-Host "✓ GCC найден: $($compiler.Source)" -ForegroundColor Green
        } else {
            $compiler = Get-Command cl -ErrorAction SilentlyContinue
            if ($compiler) {
                Write-Host "✓ MSVC найден: $($compiler.Source)" -ForegroundColor Green
            } else {
                Write-Host "✗ Компилятор C не найден (gcc или cl)" -ForegroundColor Red
                return $false
            }
        }
    } catch {
        Write-Host "✗ Компилятор C не найден" -ForegroundColor Red
        return $false
    }
    
    # Проверка Java для UPPAAL
    try {
        $javaVersion = java -version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ Java найден: $($javaVersion[0])" -ForegroundColor Green
        } else {
            Write-Host "✗ Java не найден" -ForegroundColor Red
            return $false
        }
    } catch {
        Write-Host "✗ Java не найден в PATH" -ForegroundColor Red
        return $false
    }
    
    return $true
}

# Функция создания директории результатов
function New-OutputDirectory {
    if (!(Test-Path $OutputDir)) {
        New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
        Write-Host "Создана директория результатов: $OutputDir" -ForegroundColor Green
    }
}

# Функция верификации SPIN модели
function Invoke-SpinVerification {
    param([string]$ModelPath)
    
    Write-Host "Верификация SPIN модели: $ModelPath" -ForegroundColor Cyan
    
    $outputFile = Join-Path $OutputDir "spin_plc_verification.txt"
    
    # Проверка синтаксиса
    Write-Host "  Проверка синтаксиса..." -ForegroundColor Yellow
    spin -a $ModelPath 2>&1 | Tee-Object -FilePath $outputFile
    
    if ($LASTEXITCODE -ne 0) {
        Write-Host "✗ Ошибка синтаксиса в SPIN модели" -ForegroundColor Red
        return $false
    }
    
    # Компиляция
    Write-Host "  Компиляция..." -ForegroundColor Yellow
    $compiler = Get-Command gcc -ErrorAction SilentlyContinue
    if (!$compiler) { $compiler = Get-Command cl }
    
    & $compiler.Source -o pan pan.c -DVECTORSZ=2048 2>&1 | Tee-Object -FilePath $outputFile -Append
    
    if ($LASTEXITCODE -ne 0) {
        Write-Host "✗ Ошибка компиляции" -ForegroundColor Red
        return $false
    }
    
    # Верификация
    Write-Host "  Выполнение верификации..." -ForegroundColor Yellow
    .\pan.exe -a 2>&1 | Tee-Object -FilePath $outputFile -Append
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✓ SPIN верификация завершена успешно" -ForegroundColor Green
        return $true
    } else {
        Write-Host "✗ SPIN верификация завершилась с ошибками" -ForegroundColor Red
        return $false
    }
}

# Функция верификации UPPAAL модели
function Invoke-UppaalVerification {
    param([string]$ModelPath, [string]$QueriesPath)
    
    Write-Host "Верификация UPPAAL модели: $ModelPath" -ForegroundColor Cyan
    
    $outputFile = Join-Path $OutputDir "uppaal_plc_verification.txt"
    $reportFile = Join-Path $OutputDir "uppaal_plc_report.md"
    
    # Проверка XML синтаксиса
    Write-Host "  Проверка XML синтаксиса..." -ForegroundColor Yellow
    
    try {
        [xml]$model = Get-Content $ModelPath
        Write-Host "✓ XML модель корректна" -ForegroundColor Green
    } catch {
        Write-Host "✗ Ошибка XML синтаксиса в модели" -ForegroundColor Red
        return $false
    }
    
    try {
        [xml]$queries = Get-Content $QueriesPath
        Write-Host "✓ XML запросы корректны" -ForegroundColor Green
    } catch {
        Write-Host "✗ Ошибка XML синтаксиса в запросах" -ForegroundColor Red
        return $false
    }
    
    # Создание скрипта верификации для UPPAAL
    $verificationScript = @"
// Скрипт верификации UPPAAL для ПЛК системы
// Автоматически сгенерирован

// Загрузка модели
load "$ModelPath"

// Загрузка запросов
load_queries "$QueriesPath"

// Выполнение верификации всех запросов
verify_all_queries

// Сохранение результатов
save_verification_results "$outputFile"

// Выход
exit
"@
    
    $scriptFile = Join-Path $OutputDir "uppaal_verification_script.txt"
    $verificationScript | Out-File -FilePath $scriptFile -Encoding UTF8
    
    # Создание отчета
    $report = @"
# Отчет по верификации UPPAAL модели ПЛК

## Информация о модели
- **Файл модели**: $ModelPath
- **Файл запросов**: $QueriesPath
- **Уровень безопасности**: $SafetyLevel
- **Дата верификации**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

## Инструкции по верификации

### 1. Откройте UPPAAL
Запустите UPPAAL и откройте модель: `$ModelPath`

### 2. Загрузите запросы
В UPPAAL выберите File -> Load Queries и загрузите: `$QueriesPath`

### 3. Выполните верификацию
Для каждого запроса нажмите "Check" или используйте "Verify All"

### 4. Анализируйте результаты
- ✓ (зеленая галочка) - свойство выполняется
- ✗ (красный крест) - свойство нарушается
- ⚠ (желтый треугольник) - предупреждение

## Свойства для проверки

### Безопасность
- Насосы не работают одновременно
- Аварийная остановка останавливает все насосы
- Критические условия блокируют работу насосов

### Временные ограничения
- Аварийная остановка в течение 100ms
- Запуск насоса в течение 500ms
- Остановка насоса в течение 300ms
- Цикл сканирования не более 10ms

### Живость
- Система восстанавливается из аварийного режима
- Насосы могут запускаться при нормальных условиях
- Сброс ошибок после обслуживания

## Рекомендации

1. **Для SIL1/SIL2**: Проверьте все свойства безопасности
2. **Для SIL3/SIL4**: Дополнительно проверьте временные ограничения
3. **Критические системы**: Используйте комбинацию SPIN + UPPAAL

## Следующие шаги

1. Выполните верификацию в UPPAAL
2. Проанализируйте результаты
3. Исправьте найденные ошибки
4. Повторите верификацию
5. Документируйте результаты для аудита
"@
    
    $report | Out-File -FilePath $reportFile -Encoding UTF8
    
    Write-Host "✓ UPPAAL верификация подготовлена" -ForegroundColor Green
    Write-Host "  Скрипт: $scriptFile" -ForegroundColor Yellow
    Write-Host "  Отчет: $reportFile" -ForegroundColor Yellow
    
    return $true
}

# Функция анализа результатов
function Analyze-Results {
    Write-Host "Анализ результатов верификации..." -ForegroundColor Cyan
    
    $spinResults = Join-Path $OutputDir "spin_plc_verification.txt"
    $uppaalReport = Join-Path $OutputDir "uppaal_plc_report.md"
    
    # Анализ SPIN результатов
    if (Test-Path $spinResults) {
        Write-Host "  Анализ SPIN результатов..." -ForegroundColor Yellow
        
        $content = Get-Content $spinResults -Raw
        if ($content -match "errors: 0") {
            Write-Host "✓ SPIN: Ошибки не обнаружены" -ForegroundColor Green
        } else {
            Write-Host "⚠ SPIN: Обнаружены ошибки" -ForegroundColor Yellow
        }
        
        if ($content -match "unreached in proctype") {
            Write-Host "⚠ SPIN: Обнаружен недостижимый код" -ForegroundColor Yellow
        }
    }
    
    # Создание итогового отчета
    $finalReport = Join-Path $OutputDir "plc_verification_summary.md"
    
    $summary = @"
# Итоговый отчет по верификации ПЛК системы

## Общая информация
- **Дата верификации**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")
- **Уровень безопасности**: $SafetyLevel
- **Модели**: SPIN + UPPAAL

## Результаты SPIN верификации
- **Статус**: $(if (Test-Path $spinResults) { "Выполнено" } else { "Не выполнено" })
- **Файл результатов**: $spinResults

## Результаты UPPAAL верификации
- **Статус**: Подготовлено
- **Файл отчета**: $uppaalReport

## Соответствие требованиям SIL

### SIL $SafetyLevel требования:
$(switch ($SafetyLevel) {
    "SIL1" { "- Базовые проверки безопасности`n- Логическая корректность`n- Отсутствие deadlock'ов" }
    "SIL2" { "- Расширенные проверки безопасности`n- Временные ограничения`n- Протоколы связи" }
    "SIL3" { "- Критические проверки безопасности`n- Жесткие временные ограничения`n- Отказоустойчивость" }
    "SIL4" { "- Максимальные требования безопасности`n- Доказательство корректности`n- Формальная верификация" }
})

## Рекомендации

1. **Выполните UPPAAL верификацию** для проверки временных свойств
2. **Проанализируйте все результаты** на предмет ошибок
3. **Исправьте найденные проблемы** в моделях
4. **Повторите верификацию** до устранения всех ошибок
5. **Документируйте результаты** для аудита безопасности

## Следующие шаги

1. Откройте UPPAAL и загрузите модель
2. Выполните верификацию всех TCTL свойств
3. Проанализируйте результаты
4. Создайте план исправления ошибок
5. Подготовьте документацию для сертификации
"@
    
    $summary | Out-File -FilePath $finalReport -Encoding UTF8
    
    Write-Host "✓ Итоговый отчет создан: $finalReport" -ForegroundColor Green
}

# Основная логика скрипта
if ($Help) {
    Show-Help
    exit 0
}

Write-Host "=== ПЛК ВЕРИФИКАЦИЯ С ПОМОЩЬЮ SPIN И UPPAAL ===" -ForegroundColor Cyan
Write-Host "Уровень безопасности: $SafetyLevel" -ForegroundColor Yellow
Write-Host ""

# Проверка зависимостей
if (!(Test-Dependencies)) {
    Write-Host "Ошибка: Не все зависимости установлены" -ForegroundColor Red
    Write-Host "Установите SPIN, компилятор C и Java" -ForegroundColor Yellow
    exit 1
}

# Создание директории результатов
New-OutputDirectory

# Верификация SPIN модели
$spinSuccess = $false
if (Test-Path $SpinModel) {
    $spinSuccess = Invoke-SpinVerification -ModelPath $SpinModel
} else {
    Write-Host "⚠ SPIN модель не найдена: $SpinModel" -ForegroundColor Yellow
}

# Верификация UPPAAL модели
$uppaalSuccess = $false
if (Test-Path $UppaalModel) {
    $uppaalSuccess = Invoke-UppaalVerification -ModelPath $UppaalModel -QueriesPath $UppaalQueries
} else {
    Write-Host "⚠ UPPAAL модель не найдена: $UppaalModel" -ForegroundColor Yellow
}

# Анализ результатов
Analyze-Results

# Итоговый статус
Write-Host ""
Write-Host "=== ИТОГИ ВЕРИФИКАЦИИ ===" -ForegroundColor Cyan
Write-Host "SPIN верификация: $(if ($spinSuccess) { '✓ Успешно' } else { '✗ Ошибка' })" -ForegroundColor $(if ($spinSuccess) { 'Green' } else { 'Red' })"
Write-Host "UPPAAL верификация: $(if ($uppaalSuccess) { '✓ Подготовлено' } else { '✗ Ошибка' })" -ForegroundColor $(if ($uppaalSuccess) { 'Green' } else { 'Red' })"
Write-Host ""
Write-Host "Результаты сохранены в: $OutputDir" -ForegroundColor Green
Write-Host "Для завершения UPPAAL верификации откройте отчет и следуйте инструкциям" -ForegroundColor Yellow
