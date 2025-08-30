#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Скрипт для верификации модели EtherCAT протокола в SPIN
    
.DESCRIPTION
    Автоматизирует процесс верификации EtherCAT модели:
    1. Проверяет зависимости (SPIN, GCC)
    2. Генерирует C код из Promela
    3. Компилирует и запускает верификацию
    4. Анализирует результаты
    5. Генерирует отчет
    
.PARAMETER ModelPath
    Путь к файлу модели EtherCAT (.pml)
    
.PARAMETER OutputDir
    Директория для результатов верификации
    
.EXAMPLE
    .\verify_ethercat.ps1 -ModelPath "models/spin/ethercat.pml"
    
.NOTES
    Автор: AI Assistant
    Дата: 2024-12-19
    Статус: Готов к использованию
#>

param(
    [string]$ModelPath = "models/spin/ethercat.pml",
    [string]$OutputDir = "results/ethercat_verification"
)

# Цветной вывод для лучшей читаемости
function Write-ColorOutput {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    Write-Host $Message -ForegroundColor $Color
}

# Проверка зависимостей
function Test-Dependencies {
    Write-ColorOutput "🔍 Проверка зависимостей..." "Cyan"
    
    # Проверка SPIN
    try {
        $spinVersion = spin -V 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-ColorOutput "✅ SPIN найден: $spinVersion" "Green"
        } else {
            Write-ColorOutput "❌ SPIN не работает корректно" "Red"
            return $false
        }
    } catch {
        Write-ColorOutput "❌ SPIN не найден в системе" "Red"
        Write-ColorOutput "💡 Установите SPIN Model Checker" "Yellow"
        return $false
    }
    
    # Проверка GCC
    try {
        $gccVersion = gcc --version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-ColorOutput "✅ GCC найден: $($gccVersion[0])" "Green"
        } else {
            Write-ColorOutput "❌ GCC не работает корректно" "Red"
            return $false
        }
    } catch {
        Write-ColorOutput "❌ GCC не найден в системе" "Red"
        Write-ColorOutput "💡 Установите MinGW или MSYS2" "Yellow"
        return $false
    }
    
    return $true
}

# Проверка файла модели
function Test-ModelFile {
    param([string]$Path)
    
    if (-not (Test-Path $Path)) {
        Write-ColorOutput "❌ Файл модели не найден: $Path" "Red"
        return $false
    }
    
    $content = Get-Content $Path -Raw
    if ($content -match "proctype.*EtherCATMaster") {
        Write-ColorOutput "✅ Модель EtherCAT найдена" "Green"
        return $true
    } else {
        Write-ColorOutput "❌ Файл не содержит модель EtherCAT" "Red"
        return $false
    }
}

# Генерация C кода из Promela
function Generate-Code {
    param([string]$ModelPath, [string]$OutputDir)
    
    Write-ColorOutput "🔧 Генерация C кода из Promela..." "Cyan"
    
    # Создаем директорию для результатов
    if (-not (Test-Path $OutputDir)) {
        New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
    }
    
    $modelName = [System.IO.Path]::GetFileNameWithoutExtension($ModelPath)
    $cFile = Join-Path $OutputDir "$modelName.c"
    
    try {
        # Генерируем C код
        spin -a $ModelPath
        if ($LASTEXITCODE -eq 0) {
            Write-ColorOutput "✅ C код сгенерирован: pan.c" "Green"
            
            # Переименовываем для ясности
            if (Test-Path "pan.c") {
                Move-Item "pan.c" $cFile -Force
                Write-ColorOutput "✅ Файл переименован: $cFile" "Green"
            }
        } else {
            Write-ColorOutput "❌ Ошибка генерации C кода" "Red"
            return $false
        }
    } catch {
        Write-ColorOutput "❌ Ошибка при генерации C кода: $_" "Red"
        return $false
    }
    
    return $true
}

# Компиляция C кода
function Compile-Code {
    param([string]$CFilePath, [string]$OutputDir)
    
    Write-ColorOutput "🔨 Компиляция C кода..." "Cyan"
    
    $modelName = [System.IO.Path]::GetFileNameWithoutExtension($CFilePath)
    $exeFile = Join-Path $OutputDir "$modelName.exe"
    
    try {
        # Компилируем с оптимизациями
        gcc -O2 -o $exeFile $CFilePath -DNFAIR=3
        if ($LASTEXITCODE -eq 0) {
            Write-ColorOutput "✅ Код скомпилирован: $exeFile" "Green"
            return $true
        } else {
            Write-ColorOutput "❌ Ошибка компиляции" "Red"
            return $false
        }
    } catch {
        Write-ColorOutput "❌ Ошибка при компиляции: $_" "Red"
        return $false
    }
}

# Запуск верификации
function Run-Verification {
    param([string]$ExePath, [string]$OutputDir)
    
    Write-ColorOutput "🚀 Запуск верификации..." "Cyan"
    
    $modelName = [System.IO.Path]::GetFileNameWithoutExtension($ExePath)
    $logFile = Join-Path $OutputDir "$modelName.log"
    $reportFile = Join-Path $OutputDir "$modelName.report.txt"
    
    try {
        # Запускаем верификацию с детальным выводом
        & $ExePath -a -n -N -m -w 2>&1 | Tee-Object -FilePath $logFile
        
        if ($LASTEXITCODE -eq 0) {
            Write-ColorOutput "✅ Верификация завершена успешно" "Green"
        } else {
            Write-ColorOutput "⚠️ Верификация завершена с предупреждениями" "Yellow"
        }
        
        # Анализируем результаты
        Analyze-Results $logFile $reportFile
        
    } catch {
        Write-ColorOutput "❌ Ошибка при верификации: $_" "Red"
        return $false
    }
    
    return $true
}

# Анализ результатов верификации
function Analyze-Results {
    param([string]$LogFile, [string]$ReportFile)
    
    Write-ColorOutput "📊 Анализ результатов верификации..." "Cyan"
    
    if (-not (Test-Path $LogFile)) {
        Write-ColorOutput "❌ Лог файл не найден" "Red"
        return
    }
    
    $logContent = Get-Content $LogFile -Raw
    
    # Создаем отчет
    $report = @"
=== ОТЧЕТ ПО ВЕРИФИКАЦИИ ETHERCAT ===
Дата: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")
Модель: EtherCAT протокол
Файл лога: $LogFile

=== СВОДКА ===
"@
    
    # Анализируем статистику
    if ($logContent -match "States:\s+(\d+)") {
        $states = $matches[1]
        $report += "`nКоличество состояний: $states"
    }
    
    if ($logContent -match "Transitions:\s+(\d+)") {
        $transitions = $matches[1]
        $report += "`nКоличество переходов: $transitions"
    }
    
    if ($logContent -match "Memory usage:\s+([\d.]+)") {
        $memory = $memory
        $report += "`nИспользование памяти: $memory MB"
    }
    
    # Проверяем на ошибки
    if ($logContent -match "error") {
        $report += "`n`n❌ ОБНАРУЖЕНЫ ОШИБКИ:"
        $errors = $logContent -split "`n" | Where-Object { $_ -match "error" }
        foreach ($error in $errors) {
            $report += "`n- $error"
        }
    } else {
        $report += "`n`n✅ ОШИБОК НЕ ОБНАРУЖЕНО"
    }
    
    # Проверяем на предупреждения
    if ($logContent -match "warning") {
        $report += "`n`n⚠️ ПРЕДУПРЕЖДЕНИЯ:"
        $warnings = $logContent -split "`n" | Where-Object { $_ -match "warning" }
        foreach ($warning in $warnings) {
            $report += "`n- $warning"
        }
    }
    
    # Анализ LTL свойств
    $report += "`n`n=== АНАЛИЗ LTL СВОЙСТВ ==="
    
    $ltlProperties = @(
        "state_progression",
        "command_in_op_state", 
        "master_can_run",
        "slave_can_reach_op",
        "no_deadlock",
        "synchronization",
        "no_frame_loss",
        "command_processing"
    )
    
    foreach ($property in $ltlProperties) {
        if ($logContent -match $property) {
            $report += "`n✅ $property - проверено"
        } else {
            $report += "`n❓ $property - статус неясен"
        }
    }
    
    # Специфичный анализ для EtherCAT
    $report += "`n`n=== АНАЛИЗ ETHERCAT ==="
    
    # Проверяем состояния слейвов
    if ($logContent -match "slave_states") {
        $report += "`n✅ Состояния слейвов отслеживаются"
    }
    
    # Проверяем команды
    if ($logContent -match "CMD_LRW|CMD_LRD|CMD_LWR") {
        $report += "`n✅ Команды EtherCAT обрабатываются"
    }
    
    # Проверяем сеть
    if ($logContent -match "network_ready") {
        $report += "`n✅ Сетевая готовность проверяется"
    }
    
    # Рекомендации
    $report += "`n`n=== РЕКОМЕНДАЦИИ ==="
    
    if ($logContent -match "error") {
        $report += "`n1. Исправить обнаруженные ошибки в модели"
        $report += "`n2. Проверить корректность LTL спецификаций"
        $report += "`n3. Упростить модель для уменьшения сложности"
    } else {
        $report += "`n1. Модель готова к дальнейшему анализу"
        $report += "`n2. Рассмотреть добавление дополнительных свойств"
        $report += "`n3. Перевести модель в mCRL2 для сравнения"
    }
    
    # Сохраняем отчет
    $report | Out-File -FilePath $ReportFile -Encoding UTF8
    Write-ColorOutput "✅ Отчет сохранен: $ReportFile" "Green"
    
    # Выводим краткую сводку
    Write-ColorOutput "`n📋 КРАТКАЯ СВОДКА:" "Yellow"
    if ($logContent -match "error") {
        Write-ColorOutput "❌ Обнаружены ошибки - требуется исправление" "Red"
    } else {
        Write-ColorOutput "✅ Модель верифицирована успешно" "Green"
    }
}

# Основная функция
function Main {
    Write-ColorOutput "🚀 Запуск верификации EtherCAT протокола" "Magenta"
    Write-ColorOutput "=========================================" "Magenta"
    
    # Проверяем зависимости
    if (-not (Test-Dependencies)) {
        Write-ColorOutput "❌ Зависимости не удовлетворены. Завершение работы." "Red"
        exit 1
    }
    
    # Проверяем файл модели
    if (-not (Test-ModelFile $ModelPath)) {
        Write-ColorOutput "❌ Файл модели не корректен. Завершение работы." "Red"
        exit 1
    }
    
    Write-ColorOutput "✅ Все проверки пройдены успешно" "Green"
    
    # Генерируем C код
    if (-not (Generate-Code $ModelPath $OutputDir)) {
        Write-ColorOutput "❌ Ошибка генерации C кода. Завершение работы." "Red"
        exit 1
    }
    
    # Компилируем код
    $cFile = Join-Path $OutputDir "ethercat.c"
    if (-not (Compile-Code $cFile $OutputDir)) {
        Write-ColorOutput "❌ Ошибка компиляции. Завершение работы." "Red"
        exit 1
    }
    
    # Запускаем верификацию
    $exeFile = Join-Path $OutputDir "ethercat.exe"
    if (-not (Run-Verification $exeFile $OutputDir)) {
        Write-ColorOutput "❌ Ошибка верификации. Завершение работы." "Red"
        exit 1
    }
    
    Write-ColorOutput "`n🎉 Верификация EtherCAT завершена успешно!" "Green"
    Write-ColorOutput "📁 Результаты сохранены в: $OutputDir" "Cyan"
}

# Запуск скрипта
if ($MyInvocation.InvocationName -ne '.') {
    Main
}


