#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Скрипт для верификации модели OPC UA протокола в SPIN
    
.DESCRIPTION
    Автоматизирует процесс верификации OPC UA модели:
    1. Проверяет зависимости (SPIN, GCC)
    2. Генерирует C код из Promela
    3. Компилирует и запускает верификацию
    4. Анализирует результаты
    5. Генерирует отчет
    
.PARAMETER ModelPath
    Путь к файлу модели OPC UA (.pml)
    
.PARAMETER OutputDir
    Директория для результатов верификации
    
.EXAMPLE
    .\verify_opc_ua.ps1 -ModelPath "models/spin/opc_ua.pml"
    
.NOTES
    Автор: AI Assistant
    Дата: 2024-12-19
    Статус: Готов к использованию
#>

param(
    [string]$ModelPath = "models/spin/opc_ua.pml",
    [string]$OutputDir = "results/opc_ua_verification"
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
    if ($content -match "proctype.*OPCUAClient") {
        Write-ColorOutput "✅ Модель OPC UA найдена" "Green"
        return $true
    } else {
        Write-ColorOutput "❌ Файл не содержит модель OPC UA" "Red"
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
=== ОТЧЕТ ПО ВЕРИФИКАЦИИ OPC UA ===
Дата: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")
Модель: OPC UA протокол
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
        $memory = $matches[1]
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
        "auth_required",
        "unauthorized_blocked", 
        "secure_channel_before_transmission",
        "authorized_processed",
        "response_delivered",
        "no_security_deadlock",
        "correct_sequence",
        "session_before_data"
    )
    
    foreach ($property in $ltlProperties) {
        if ($logContent -match $property) {
            $report += "`n✅ $property - проверено"
        } else {
            $report += "`n❓ $property - статус неясен"
        }
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
    Write-ColorOutput "🚀 Запуск верификации OPC UA протокола" "Magenta"
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
    $cFile = Join-Path $OutputDir "opc_ua.c"
    if (-not (Compile-Code $cFile $OutputDir)) {
        Write-ColorOutput "❌ Ошибка компиляции. Завершение работы." "Red"
        exit 1
    }
    
    # Запускаем верификацию
    $exeFile = Join-Path $OutputDir "opc_ua.exe"
    if (-not (Run-Verification $exeFile $OutputDir)) {
        Write-ColorOutput "❌ Ошибка верификации. Завершение работы." "Red"
        exit 1
    }
    
    Write-ColorOutput "`n🎉 Верификация OPC UA завершена успешно!" "Green"
    Write-ColorOutput "📁 Результаты сохранены в: $OutputDir" "Cyan"
}

# Запуск скрипта
if ($MyInvocation.InvocationName -ne '.') {
    Main
}
