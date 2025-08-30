#!/usr/bin/env pwsh
# Скрипт для запуска Spot (Library for ω-Automata)
# Spot - библиотека для работы с автоматами Бюхи и временной логикой

param(
    [Parameter(Mandatory=$false)]
    [string]$ModelFile = "models/spot/traffic_light.py",
    
    [Parameter(Mandatory=$false)]
    [switch]$Help,
    
    [Parameter(Mandatory=$false)]
    [switch]$Verbose,
    
    [Parameter(Mandatory=$false)]
    [string]$OutputFile = "",
    
    [Parameter(Mandatory=$false)]
    [ValidateSet("basic", "traffic_light", "advanced", "all")]
    [string]$DemoType = "all"
)

# Функция вывода справки
function Show-Help {
    Write-Host @"
Spot Runner Script
==================

Использование:
    .\run_spot.ps1 [-ModelFile <путь>] [-Help] [-Verbose] [-OutputFile <путь>] [-DemoType <тип>]

Параметры:
    -ModelFile     Путь к Python файлу модели (по умолчанию: models/spot/traffic_light.py)
    -Help          Показать эту справку
    -Verbose       Подробный вывод
    -OutputFile    Файл для сохранения результатов
    -DemoType      Тип демонстрации: basic, traffic_light, advanced, all (по умолчанию: all)

Примеры:
    .\run_spot.ps1
    .\run_spot.ps1 -ModelFile "models/spot/advanced_automata.py"
    .\run_spot.ps1 -Verbose -DemoType "basic" -OutputFile "results/spot_output.txt"

Spot особенности:
    - Библиотека для работы с ω-автоматами
    - Гибкость и кастомизация
    - Подходит для исследований и разработки новых алгоритмов
    - Python интерфейс
"@
}

# Проверка наличия Python
function Test-Python {
    try {
        $version = python --version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ Python найден: $version" -ForegroundColor Green
            return $true
        }
    }
    catch {
        try {
            $version = python3 --version 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ Python3 найден: $version" -ForegroundColor Green
                return $true
            }
        }
        catch {
            Write-Host "✗ Python не найден в PATH" -ForegroundColor Red
            Write-Host "Установите Python:" -ForegroundColor Yellow
            Write-Host "  winget install Python.Python.3.11" -ForegroundColor Cyan
            Write-Host "  или скачайте с: https://www.python.org/" -ForegroundColor Cyan
            return $false
        }
    }
    return $false
}

# Проверка наличия Spot
function Test-Spot {
    try {
        $result = python -c "import spot; print(spot.version())" 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ Spot найден: версия $result" -ForegroundColor Green
            return $true
        }
    }
    catch {
        try {
            $result = python3 -c "import spot; print(spot.version())" 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ Spot найден (python3): версия $result" -ForegroundColor Green
                return $true
            }
        }
        catch {
            Write-Host "✗ Spot не найден" -ForegroundColor Red
            Write-Host "Установите Spot:" -ForegroundColor Yellow
            Write-Host "  pip install spot" -ForegroundColor Cyan
            Write-Host "  или pip3 install spot" -ForegroundColor Cyan
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
        Get-ChildItem "models/spot/" -Filter "*.py" | ForEach-Object {
            Write-Host "  - $($_.Name)" -ForegroundColor Cyan
        }
        return $false
    }
    
    Write-Host "✓ Файл модели найден: $file" -ForegroundColor Green
    return $true
}

# Определение команды Python
function Get-PythonCommand {
    try {
        if (Get-Command "python" -ErrorAction SilentlyContinue) {
            return "python"
        } elseif (Get-Command "python3" -ErrorAction SilentlyContinue) {
            return "python3"
        } else {
            return "python"
        }
    }
    catch {
        return "python"
    }
}

# Основная функция верификации
function Invoke-SpotVerification {
    param(
        [string]$modelFile,
        [string]$demoType,
        [string]$outputFile = ""
    )
    
    Write-Host "`n🚀 Запуск Spot демонстрации..." -ForegroundColor Magenta
    Write-Host "Модель: $modelFile" -ForegroundColor Cyan
    Write-Host "Тип демонстрации: $demoType" -ForegroundColor Cyan
    
    # Определение команды и аргументов
    $command = Get-PythonCommand
    $args = @($modelFile)
    
    if ($Verbose) {
        Write-Host "Команда: $command $($args -join ' ')" -ForegroundColor Gray
    }
    
    # Запуск Spot
    try {
        if ($outputFile -and $outputFile -ne "") {
            Write-Host "Результаты будут сохранены в: $outputFile" -ForegroundColor Yellow
            & $command @args | Tee-Object -FilePath $outputFile
        } else {
            & $command @args
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "`n✅ Spot демонстрация завершена успешно!" -ForegroundColor Green
        } else {
            Write-Host "`n⚠️ Spot завершился с кодом: $LASTEXITCODE" -ForegroundColor Yellow
        }
    }
    catch {
        Write-Host "`n❌ Ошибка при запуске Spot: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Функция анализа результатов
function Analyze-SpotResults {
    param([string]$outputFile)
    
    if (-not (Test-Path $outputFile)) {
        Write-Host "Файл результатов не найден для анализа" -ForegroundColor Yellow
        return
    }
    
    Write-Host "`n📊 Анализ результатов Spot..." -ForegroundColor Magenta
    
    $content = Get-Content $outputFile -Raw
    
    # Поиск результатов верификации
    if ($content -match "Демонстрация завершена успешно") {
        Write-Host "✅ Демонстрация Spot выполнена успешно" -ForegroundColor Green
    }
    
    # Поиск информации о версии
    if ($content -match "Spot версия: (.+)") {
        $version = $matches[1]
        Write-Host "🔧 Версия Spot: $version" -ForegroundColor Cyan
    }
    
    # Поиск информации о автоматах
    if ($content -match "(\d+) состояний") {
        $states = $matches[1]
        Write-Host "📈 Состояний в автомате: $states" -ForegroundColor Cyan
    }
    
    # Поиск информации о формулах
    if ($content -match "Формула.*: (.+)") {
        $formula = $matches[1]
        Write-Host "📝 LTL формула: $formula" -ForegroundColor Cyan
    }
}

# Главная логика скрипта
function Main {
    if ($Help) {
        Show-Help
        return
    }
    
    Write-Host "🔍 Spot Library for ω-Automata" -ForegroundColor Blue
    Write-Host "==============================" -ForegroundColor Blue
    
    # Проверка Python
    if (-not (Test-Python)) {
        return
    }
    
    # Проверка Spot
    if (-not (Test-Spot)) {
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
    
    # Запуск демонстрации
    Invoke-SpotVerification -modelFile $ModelFile -demoType $DemoType -outputFile $OutputFile
    
    # Анализ результатов
    if ($OutputFile -and $OutputFile -ne "") {
        Analyze-SpotResults -outputFile $OutputFile
    }
    
    Write-Host "`n✨ Готово!" -ForegroundColor Green
}

# Запуск главной функции
Main
