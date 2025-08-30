#!/usr/bin/env pwsh
# -*- coding: utf-8 -*-
<#
.SYNOPSIS
    Демонстрация продвинутых методов формальной верификации
    
.DESCRIPTION
    Этот скрипт демонстрирует три продвинутых метода верификации:
    1. IC3/PDR - Property Directed Reachability
    2. Interpolation - Генерация инвариантов из контрпримеров
    3. Abstraction Refinement - Работа с абстрактными моделями
    
.PARAMETER Method
    Метод для демонстрации: ic3_pdr, interpolation, abstraction, all
    
.PARAMETER Model
    Модель для анализа (опционально)
    
.EXAMPLE
    .\demo_advanced_methods.ps1 -Method ic3_pdr
    .\demo_advanced_methods.ps1 -Method all -Model "modbus_tcp"
    
.NOTES
    Автор: Senior Developer
    Дата: 2024-12-19
    Версия: 1.0
#>

param(
    [Parameter(Mandatory=$false)]
    [ValidateSet("ic3_pdr", "interpolation", "abstraction", "all")]
    [string]$Method = "all",
    
    [Parameter(Mandatory=$false)]
    [string]$Model = ""
)

# Цвета для вывода
$Colors = @{
    Header = "Cyan"
    Success = "Green"
    Warning = "Yellow"
    Error = "Red"
    Info = "Blue"
    Method = "Magenta"
}

# Функция для цветного вывода
function Write-ColorOutput {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    Write-Host $Message -ForegroundColor $Colors[$Color]
}

# Функция для вывода заголовка
function Write-Header {
    param([string]$Title)
    Write-ColorOutput "`n" -Color Header
    Write-ColorOutput "=" * 80 -Color Header
    Write-ColorOutput " $Title" -Color Header
    Write-ColorOutput "=" * 80 -Color Header
    Write-ColorOutput ""
}

# Функция для вывода информации о методе
function Write-MethodInfo {
    param(
        [string]$MethodName,
        [string]$Description,
        [string]$Problem,
        [string]$Solution
    )
    Write-ColorOutput "🔧 $MethodName" -Color Method
    Write-ColorOutput "   Описание: $Description" -Color Info
    Write-ColorOutput "   Проблема: $Problem" -Color Warning
    Write-ColorOutput "   Решение: $Solution" -Color Success
    Write-ColorOutput ""
}

# Функция для демонстрации IC3/PDR
function Demo-IC3PDR {
    Write-Header "IC3/PDR - Property Directed Reachability"
    
    Write-MethodInfo `
        "IC3/PDR" `
        "Автоматическая генерация инвариантов для сложных систем" `
        "K-индукция не может найти сложные инварианты" `
        "Автоматически генерирует инварианты"
    
    # Показываем доступные модели
    Write-ColorOutput "📁 Доступные модели IC3/PDR:" -Color Info
    $models = Get-ChildItem "models/ic3_pdr" -Filter "*.sal" | ForEach-Object { $_.BaseName }
    
    foreach ($model in $models) {
        Write-ColorOutput "   ✅ $model.sal" -Color Success
    }
    
    # Показываем конфигурацию
    Write-ColorOutput "`n⚙️ Конфигурация IC3/PDR:" -Color Info
    if (Test-Path "config/ic3_pdr.conf") {
        $config = Get-Content "config/ic3_pdr.conf" | Select-String "enabled|invariant_generation|strengthening_iterations"
        foreach ($line in $config) {
            Write-ColorOutput "   $line" -Color Info
        }
    }
    
    # Показываем примеры проблем
    Write-ColorOutput "`n🎯 Примеры проблем, решаемых IC3/PDR:" -Color Info
    Write-ColorOutput "   • Сложные инварианты Modbus TCP" -Color Warning
    Write-ColorOutput "   • Свойства безопасности EtherCAT" -Color Warning
    Write-ColorOutput "   • Инварианты промышленных протоколов" -Color Warning
    
    Write-ColorOutput "`n✅ IC3/PDR демонстрация завершена" -Color Success
}

# Функция для демонстрации Interpolation
function Demo-Interpolation {
    Write-Header "Interpolation - Генерация инвариантов из контрпримеров"
    
    Write-MethodInfo `
        "Interpolation" `
        "Генерация инвариантов из контрпримеров для временных свойств" `
        "Сложные временные свойства в UPPAAL" `
        "Генерирует инварианты из контрпримеров"
    
    # Показываем доступные модели
    Write-ColorOutput "📁 Доступные модели Interpolation:" -Color Info
    $models = Get-ChildItem "models/interpolation" -Filter "*.sal" | ForEach-Object { $_.BaseName }
    
    foreach ($model in $models) {
        Write-ColorOutput "   ✅ $model.sal" -Color Success
    }
    
    # Показываем конфигурацию
    Write-ColorOutput "`n⚙️ Конфигурация Interpolation:" -Color Info
    if (Test-Path "config/interpolation.conf") {
        $config = Get-Content "config/interpolation.conf" | Select-String "enabled|temporal_interpolation|unsat_core_analysis"
        foreach ($line in $config) {
            Write-ColorOutput "   $line" -Color Info
        }
    }
    
    # Показываем примеры проблем
    Write-ColorOutput "`n🎯 Примеры проблем, решаемых Interpolation:" -Color Info
    Write-ColorOutput "   • Временные нарушения в системах светофора" -Color Warning
    Write-ColorOutput "   • Дедлайны PLC систем" -Color Warning
    Write-ColorOutput "   • Таймауты промышленных протоколов" -Color Warning
    
    Write-ColorOutput "`n✅ Interpolation демонстрация завершена" -Color Success
}

# Функция для демонстрации Abstraction Refinement
function Demo-AbstractionRefinement {
    Write-Header "Abstraction Refinement - Работа с абстрактными моделями"
    
    Write-MethodInfo `
        "Abstraction Refinement" `
        "Работа с абстрактными моделями для решения проблемы взрыва состояний" `
        "Взрыв состояний в больших системах" `
        "Работает с абстрактными моделями"
    
    # Показываем доступные модели
    Write-ColorOutput "📁 Доступные модели Abstraction Refinement:" -Color Info
    $models = Get-ChildItem "models/abstraction" -Filter "*.sal" | ForEach-Object { $_.BaseName }
    
    foreach ($model in $models) {
        Write-ColorOutput "   ✅ $model.sal" -Color Success
    }
    
    # Показываем конфигурацию
    Write-ColorOutput "`n⚙️ Конфигурация Abstraction Refinement:" -Color Info
    if (Test-Path "config/abstraction.conf") {
        $config = Get-Content "config/abstraction.conf" | Select-String "enabled|abstraction_method|max_abstract_states"
        foreach ($line in $config) {
            Write-ColorOutput "   $line" -Color Info
        }
    }
    
    # Показываем примеры проблем
    Write-ColorOutput "`n🎯 Примеры проблем, решаемых Abstraction Refinement:" -Color Info
    Write-ColorOutput "   • Сети с 100+ узлами" -Color Warning
    Write-ColorOutput "   • Промышленные системы управления" -Color Warning
    Write-ColorOutput "   • IoT системы" -Color Warning
    
    Write-ColorOutput "`n✅ Abstraction Refinement демонстрация завершена" -Color Success
}

# Функция для сравнения методов
function Compare-Methods {
    Write-Header "Сравнение методов верификации"
    
    $comparison = @"
| Метод | Решает проблему | Сложность | Время выполнения | Применимость |
|-------|----------------|-----------|------------------|--------------|
| K-индукция | Простые инварианты | Низкая | Быстро | Простые системы |
| IC3/PDR | Сложные инварианты | Средняя | Средне | Промышленные протоколы |
| Interpolation | Временные свойства | Средняя | Средне | Системы реального времени |
| Abstraction Refinement | Взрыв состояний | Высокая | Медленно | Большие системы |
"@
    
    Write-ColorOutput $comparison -Color Info
    
    Write-ColorOutput "`n🎯 Рекомендации по выбору метода:" -Color Info
    Write-ColorOutput "   • Простые протоколы (до 100 состояний): K-индукция" -Color Success
    Write-ColorOutput "   • Промышленные протоколы (100-1000 состояний): IC3/PDR" -Color Success
    Write-ColorOutput "   • Системы реального времени (1000+ состояний): Interpolation" -Color Success
    Write-ColorOutput "   • Большие сети (10000+ состояний): Abstraction Refinement" -Color Success
}

# Функция для анализа конкретной модели
function Analyze-Model {
    param([string]$ModelName)
    
    Write-Header "Анализ модели: $ModelName"
    
    # Определяем тип модели
    if ($ModelName -like "*modbus*" -or $ModelName -like "*ethercat*") {
        Write-ColorOutput "🔍 Рекомендуемый метод: IC3/PDR" -Color Method
        Write-ColorOutput "   Причина: Сложные промышленные протоколы требуют автоматической генерации инвариантов" -Color Info
    }
    elseif ($ModelName -like "*traffic*" -or $ModelName -like "*timer*") {
        Write-ColorOutput "🔍 Рекомендуемый метод: Interpolation" -Color Method
        Write-ColorOutput "   Причина: Временные системы требуют анализа временных нарушений" -Color Info
    }
    elseif ($ModelName -like "*network*" -or $ModelName -like "*distributed*") {
        Write-ColorOutput "🔍 Рекомендуемый метод: Abstraction Refinement" -Color Method
        Write-ColorOutput "   Причина: Большие сети требуют работы с абстрактными моделями" -Color Info
    }
    else {
        Write-ColorOutput "🔍 Рекомендуемый метод: K-индукция" -Color Method
        Write-ColorOutput "   Причина: Простые системы не требуют продвинутых методов" -Color Info
    }
}

# Основная логика скрипта
function Main {
    Write-Header "Демонстрация продвинутых методов формальной верификации"
    
    Write-ColorOutput "🎯 Цель: Показать эволюцию методов от простых к сложным" -Color Info
    Write-ColorOutput "📚 Документация: docs/advanced_verification_methods.md" -Color Info
    Write-ColorOutput ""
    
    # Проверяем наличие конфигурационных файлов
    Write-ColorOutput "🔍 Проверка конфигурации:" -Color Info
    $configs = @("ic3_pdr.conf", "interpolation.conf", "abstraction.conf")
    
    foreach ($config in $configs) {
        if (Test-Path "config/$config") {
            Write-ColorOutput "   ✅ config/$config" -Color Success
        } else {
            Write-ColorOutput "   ❌ config/$config" -Color Error
        }
    }
    
    # Проверяем наличие моделей
    Write-ColorOutput "`n🔍 Проверка моделей:" -Color Info
    $modelDirs = @("ic3_pdr", "interpolation", "abstraction")
    
    foreach ($dir in $modelDirs) {
        if (Test-Path "models/$dir") {
            $count = (Get-ChildItem "models/$dir" -Filter "*.sal").Count
            Write-ColorOutput "   ✅ models/$dir ($count моделей)" -Color Success
        } else {
            Write-ColorOutput "   ❌ models/$dir" -Color Error
        }
    }
    
    # Демонстрируем выбранные методы
    switch ($Method) {
        "ic3_pdr" { Demo-IC3PDR }
        "interpolation" { Demo-Interpolation }
        "abstraction" { Demo-AbstractionRefinement }
        "all" {
            Demo-IC3PDR
            Demo-Interpolation
            Demo-AbstractionRefinement
            Compare-Methods
        }
    }
    
    # Анализируем конкретную модель, если указана
    if ($Model) {
        Analyze-Model $Model
    }
    
    Write-Header "Демонстрация завершена"
    Write-ColorOutput "📈 Следующий этап: Интеграция и тестирование" -Color Info
    Write-ColorOutput "📚 Дополнительная информация: docs/advanced_verification_methods.md" -Color Info
}

# Запуск основной функции
try {
    Main
} catch {
    Write-ColorOutput "❌ Ошибка выполнения: $($_.Exception.Message)" -Color Error
    exit 1
}
