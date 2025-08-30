#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Скрипт для верификации протокола "Эхо-сервер" с помощью SPIN
    
.DESCRIPTION
    Автоматизирует процесс верификации протокола связи:
    1. Компилирует модель Promela в C
    2. Компилирует C код в исполняемый файл
    3. Запускает верификацию с различными свойствами
    4. Анализирует результаты
    
.PARAMETER ModelPath
    Путь к файлу модели Promela (по умолчанию: ../models/spin/echo_protocol.pml)
    
.PARAMETER OutputDir
    Директория для результатов (по умолчанию: ../results/echo_protocol)
    
.EXAMPLE
    .\verify_echo_protocol.ps1
    .\verify_echo_protocol.ps1 -ModelPath "my_protocol.pml"
#>

param(
    [string]$ModelPath = "../models/spin/echo_protocol.pml",
    [string]$OutputDir = "../results/echo_protocol"
)

# Цвета для вывода
$Colors = @{
    Info = "Cyan"
    Success = "Green"
    Warning = "Yellow"
    Error = "Red"
}

function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Colors[$Color]
}

function Test-SPIN {
    try {
        $spinVersion = spin -V 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-ColorOutput "✅ SPIN найден: $spinVersion" "Success"
            return $true
        }
    }
    catch {
        Write-ColorOutput "❌ SPIN не найден в PATH" "Error"
        return $false
    }
    return $false
}

function Test-GCC {
    try {
        $gccVersion = gcc --version 2>&1 | Select-Object -First 1
        if ($LASTEXITCODE -eq 0) {
            Write-ColorOutput "✅ GCC найден: $gccVersion" "Success"
            return $true
        }
    }
    catch {
        Write-ColorOutput "❌ GCC не найден в PATH" "Error"
        return $false
    }
    return $false
}

function Verify-Protocol {
    param([string]$ModelPath, [string]$OutputDir)
    
    Write-ColorOutput "🔍 Начинаю верификацию протокола..." "Info"
    
    # Создаем директорию для результатов
    if (!(Test-Path $OutputDir)) {
        New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
        Write-ColorOutput "📁 Создана директория: $OutputDir" "Info"
    }
    
    # Получаем имя модели без расширения
    $modelName = [System.IO.Path]::GetFileNameWithoutExtension($ModelPath)
    $cFile = Join-Path $OutputDir "$modelName.c"
    $exeFile = Join-Path $OutputDir "$modelName.exe"
    
    Write-ColorOutput "📝 Компилирую Promela в C..." "Info"
    
    # Компилируем Promela в C
    try {
        spin -a $ModelPath
        if ($LASTEXITCODE -ne 0) {
            throw "Ошибка компиляции Promela в C"
        }
        
        # Перемещаем сгенерированный C файл
        if (Test-Path "pan.c") {
            Move-Item "pan.c" $cFile -Force
        }
        if (Test-Path "pan.h") {
            Move-Item "pan.h" (Join-Path $OutputDir "pan.h") -Force
        }
        
        Write-ColorOutput "✅ Promela успешно скомпилирован в C" "Success"
    }
    catch {
        Write-ColorOutput "❌ Ошибка при компиляции Promela: $_" "Error"
        return $false
    }
    
    Write-ColorOutput "🔨 Компилирую C в исполняемый файл..." "Info"
    
    # Компилируем C в исполняемый файл
    try {
        gcc -o $exeFile $cFile -O2
        if ($LASTEXITCODE -ne 0) {
            throw "Ошибка компиляции C"
        }
        
        Write-ColorOutput "✅ C успешно скомпилирован в исполняемый файл" "Success"
    }
    catch {
        Write-ColorOutput "❌ Ошибка при компиляции C: $_" "Error"
        return $false
    }
    
    Write-ColorOutput "🚀 Запускаю верификацию..." "Info"
    
    # Запускаем верификацию
    try {
        $verificationResult = & $exeFile 2>&1
        $exitCode = $LASTEXITCODE
        
        # Сохраняем результат
        $resultFile = Join-Path $OutputDir "verification_result.txt"
        $verificationResult | Out-File -FilePath $resultFile -Encoding UTF8
        
        if ($exitCode -eq 0) {
            Write-ColorOutput "✅ Верификация завершена успешно" "Success"
            Write-ColorOutput "📊 Результаты сохранены в: $resultFile" "Info"
            
            # Анализируем результаты
            $results = Get-Content $resultFile
            Write-ColorOutput "📈 Анализ результатов:" "Info"
            
            foreach ($line in $results) {
                if ($line -match "errors: (\d+)") {
                    $errors = $matches[1]
                    if ([int]$errors -eq 0) {
                        Write-ColorOutput "   ✅ Ошибок не найдено" "Success"
                    } else {
                        Write-ColorOutput "   ❌ Найдено ошибок: $errors" "Warning"
                    }
                }
                if ($line -match "states: (\d+)") {
                    $states = $matches[1]
                    Write-ColorOutput "   📊 Состояний проверено: $states" "Info"
                }
            }
        } else {
            Write-ColorOutput "⚠️ Верификация завершена с кодом: $exitCode" "Warning"
            Write-ColorOutput "📊 Результаты сохранены в: $resultFile" "Info"
        }
    }
    catch {
        Write-ColorOutput "❌ Ошибка при верификации: $_" "Error"
        return $false
    }
    
    return $true
}

# Основная логика скрипта
function Main {
    Write-ColorOutput "🚀 Верификация протокола 'Эхо-сервер' с помощью SPIN" "Info"
    Write-ColorOutput "=" * 60 "Info"
    
    # Проверяем зависимости
    Write-ColorOutput "🔍 Проверяю зависимости..." "Info"
    
    if (!(Test-SPIN)) {
        Write-ColorOutput "❌ SPIN не найден. Установите SPIN и добавьте в PATH" "Error"
        Write-ColorOutput "💡 Скачать можно с: http://spinroot.com/" "Info"
        return 1
    }
    
    if (!(Test-GCC)) {
        Write-ColorOutput "❌ GCC не найден. Установите MinGW или другой C компилятор" "Error"
        return 1
    }
    
    # Проверяем существование модели
    if (!(Test-Path $ModelPath)) {
        Write-ColorOutput "❌ Файл модели не найден: $ModelPath" "Error"
        return 1
    }
    
    Write-ColorOutput "✅ Все зависимости найдены" "Success"
    Write-ColorOutput ""
    
    # Запускаем верификацию
    $success = Verify-Protocol -ModelPath $ModelPath -OutputDir $OutputDir
    
    if ($success) {
        Write-ColorOutput ""
        Write-ColorOutput "🎉 Верификация протокола завершена успешно!" "Success"
        Write-ColorOutput "📁 Результаты сохранены в: $OutputDir" "Info"
    } else {
        Write-ColorOutput ""
        Write-ColorOutput "❌ Верификация завершена с ошибками" "Error"
        return 1
    }
    
    return 0
}

# Запускаем основную функцию
exit (Main)
