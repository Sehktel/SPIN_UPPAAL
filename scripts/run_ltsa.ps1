#!/usr/bin/env pwsh
# Скрипт для запуска LTSA (Labelled Transition System Analyser)
# LTSA использует FSP (Finite State Processes) для простого моделирования

param(
    [Parameter(Mandatory=$false)]
    [string]$ModelFile = "models/ltsa/traffic_light.fsp",
    
    [Parameter(Mandatory=$false)]
    [switch]$Help,
    
    [Parameter(Mandatory=$false)]
    [switch]$Verbose,
    
    [Parameter(Mandatory=$false)]
    [string]$OutputFile = "",
    
    [Parameter(Mandatory=$false)]
    [ValidateSet("safety", "liveness", "deadlock", "all")]
    [string]$CheckType = "all"
)

# Функция вывода справки
function Show-Help {
    Write-Host @"
LTSA Runner Script
==================

Использование:
    .\run_ltsa.ps1 [-ModelFile <путь>] [-Help] [-Verbose] [-OutputFile <путь>] [-CheckType <тип>]

Параметры:
    -ModelFile     Путь к FSP файлу модели (по умолчанию: models/ltsa/traffic_light.fsp)
    -Help          Показать эту справку
    -Verbose       Подробный вывод
    -OutputFile    Файл для сохранения результатов
    -CheckType     Тип проверки: safety, liveness, deadlock, all (по умолчанию: all)

Примеры:
    .\run_ltsa.ps1
    .\run_ltsa.ps1 -ModelFile "models/ltsa/embedded_system.fsp"
    .\run_ltsa.ps1 -Verbose -CheckType "safety" -OutputFile "results/ltsa_output.txt"

LTSA особенности:
    - Простой язык FSP (Finite State Processes)
    - Легкость использования и понимания
    - Подходит для обучения и прототипирования
    - Графический интерфейс для анализа
"@
}

# Проверка наличия LTSA
function Test-LTSA {
    try {
        $version = ltsa -version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ LTSA найден: $version" -ForegroundColor Green
            return $true
        }
    }
    catch {
        try {
            $version = ltsa.exe -version 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ LTSA найден (ltsa.exe): $version" -ForegroundColor Green
                return $true
            }
        }
        catch {
            Write-Host "✗ LTSA не найден в PATH" -ForegroundColor Red
            Write-Host "Установите LTSA:" -ForegroundColor Yellow
            Write-Host "  Скачайте с: http://www.doc.ic.ac.uk/ltsa/" -ForegroundColor Cyan
            Write-Host "  Добавьте в PATH: C:\ltsa\bin" -ForegroundColor Cyan
            return $false
        }
    }
    return $false
}

# Проверка существования файла модели
function Test-ModelFile {
    param([string]$file)
    
    if (-not (Test-Path $file)) {
        Write-Host "✗ Файл модели не найден: $file" -ForegroundColor Red
        Write-Host "Доступные модели:" -ForegroundColor Yellow
        Get-ChildItem "models/ltsa/" -Filter "*.fsp" | ForEach-Object {
            Write-Host "  - $($_.Name)" -ForegroundColor Cyan
        }
        return $false
    }
    
    Write-Host "✓ Файл модели найден: $file" -ForegroundColor Green
    return $true
}

# Определение аргументов LTSA на основе типа проверки
function Get-LTSAArguments {
    param([string]$checkType)
    
    switch ($checkType) {
        "safety" { 
            return @("-safety", "-verbose")
        }
        "liveness" { 
            return @("-liveness", "-verbose")
        }
        "deadlock" { 
            return @("-deadlock", "-verbose")
        }
        "all" { 
            return @("-all", "-verbose")
        }
        default { 
            return @("-all", "-verbose")
        }
    }
}

# Основная функция верификации
function Invoke-LTSAVerification {
    param(
        [string]$modelFile,
        [string]$checkType,
        [string]$outputFile = ""
    )
    
    Write-Host "`n🚀 Запуск LTSA верификации..." -ForegroundColor Magenta
    Write-Host "Модель: $modelFile" -ForegroundColor Cyan
    Write-Host "Тип проверки: $checkType" -ForegroundColor Cyan
    
    # Определение команды и аргументов
    $command = "ltsa"
    $args = Get-LTSAArguments -checkType $checkType
    $args += $modelFile
    
    if ($Verbose) {
        Write-Host "Команда: $command $($args -join ' ')" -ForegroundColor Gray
    }
    
    # Запуск LTSA
    try {
        if ($outputFile -and $outputFile -ne "") {
            Write-Host "Результаты будут сохранены в: $outputFile" -ForegroundColor Yellow
            & $command @args | Tee-Object -FilePath $outputFile
        } else {
            & $command @args
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "`n✅ LTSA верификация завершена успешно!" -ForegroundColor Green
        } else {
            Write-Host "`n⚠️ LTSA завершился с кодом: $LASTEXITCODE" -ForegroundColor Yellow
        }
    }
    catch {
        Write-Host "`n❌ Ошибка при запуске LTSA: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Функция анализа результатов
function Analyze-LTSAResults {
    param([string]$outputFile)
    
    if (-not (Test-Path $outputFile)) {
        Write-Host "Файл результатов не найден для анализа" -ForegroundColor Yellow
        return
    }
    
    Write-Host "`n📊 Анализ результатов LTSA..." -ForegroundColor Magenta
    
    $content = Get-Content $outputFile -Raw
    
    # Поиск результатов верификации
    if ($content -match "safety.*violation") {
        Write-Host "❌ Найдены нарушения безопасности!" -ForegroundColor Red
    } elseif ($content -match "safety.*satisfied") {
        Write-Host "✅ Безопасность удовлетворена" -ForegroundColor Green
    }
    
    # Поиск информации о состояниях
    if ($content -match "states.*: (\d+)") {
        $states = $matches[1]
        Write-Host "📈 Состояний: $states" -ForegroundColor Cyan
    }
    
    # Поиск времени выполнения
    if ($content -match "time.*: ([\d.]+)") {
        $time = $matches[1]
        Write-Host "⏱️ Время выполнения: $time сек" -ForegroundColor Cyan
    }
    
    # Поиск информации о переходах
    if ($content -match "transitions.*: (\d+)") {
        $transitions = $matches[1]
        Write-Host "🔄 Переходов: $transitions" -ForegroundColor Cyan
    }
}

# Главная логика скрипта
function Main {
    if ($Help) {
        Show-Help
        return
    }
    
    Write-Host "🔍 LTSA Labelled Transition System Analyser" -ForegroundColor Blue
    Write-Host "=============================================" -ForegroundColor Blue
    
    # Проверка LTSA
    if (-not (Test-LTSA)) {
        return
    }
    
    # Проверка файла модели
    if (-not (Test-ModelFile $ModelFile)) {
        return
    }
    
    # Создание директории для результатов
    if ($OutputFile -and $OutputFile -ne "") {
        $outputDir = Split-Path $OutputFile -Parent
        if ($outputDir -and -not (Test-Path $outputDir)) {
            New-Item -ItemType Directory -Path $outputDir -Force | Out-Null
        }
    }
    
    # Запуск верификации
    Invoke-LTSAVerification -modelFile $ModelFile -checkType $CheckType -outputFile $OutputFile
    
    # Анализ результатов
    if ($OutputFile -and $OutputFile -ne "") {
        Analyze-LTSAResults -outputFile $OutputFile
    }
    
    Write-Host "`n✨ Готово!" -ForegroundColor Green
}

# Запуск главной функции
Main


