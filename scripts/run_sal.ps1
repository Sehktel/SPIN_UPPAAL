#!/usr/bin/env pwsh
# Скрипт для запуска SAL (Symbolic Analysis Laboratory)
# SAL использует Yices SMT-решатель для эффективной верификации

param(
    [Parameter(Mandatory=$false)]
    [string]$ModelFile = "models/sal/traffic_light.sal",
    
    [Parameter(Mandatory=$false)]
    [switch]$Help,
    
    [Parameter(Mandatory=$false)]
    [switch]$Verbose,
    
    [Parameter(Mandatory=$false)]
    [string]$OutputFile = "",
    
    [Parameter(Mandatory=$false)]
    [ValidateSet("mc", "bmc", "k-induction", "invariant")]
    [string]$Method = "mc"
)

# Функция вывода справки
function Show-Help {
    Write-Host @"
SAL Runner Script
=================

Использование:
    .\run_sal.ps1 [-ModelFile <путь>] [-Help] [-Verbose] [-OutputFile <путь>] [-Method <метод>]

Параметры:
    -ModelFile     Путь к SAL файлу модели (по умолчанию: models/sal/traffic_light.sal)
    -Help          Показать эту справку
    -Verbose       Подробный вывод
    -OutputFile    Файл для сохранения результатов
    -Method        Метод верификации: mc, bmc, k-induction, invariant (по умолчанию: mc)

Примеры:
    .\run_sal.ps1
    .\run_sal.ps1 -ModelFile "models/sal/distributed_system.sal"
    .\run_sal.ps1 -Verbose -Method "bmc" -OutputFile "results/sal_output.txt"

SAL особенности:
    - SMT-решатель Yices для эффективной верификации
    - Модульный подход к моделированию
    - Поддержка арифметических ограничений
    - Эффективен для распределенных систем и систем реального времени
"@
}

# Проверка наличия SAL
function Test-SAL {
    try {
        $version = sal-smc -version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ SAL найден: $version" -ForegroundColor Green
            return $true
        }
    }
    catch {
        try {
            $version = sal-inf-bmc -version 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ SAL найден (inf-bmc): $version" -ForegroundColor Green
                return $true
            }
        }
        catch {
            Write-Host "✗ SAL не найден в PATH" -ForegroundColor Red
            Write-Host "Установите SAL:" -ForegroundColor Yellow
            Write-Host "  Скачайте с: https://sal.csl.sri.com/" -ForegroundColor Cyan
            Write-Host "  Добавьте в PATH: C:\sal\bin" -ForegroundColor Cyan
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
        Get-ChildItem "models/sal/" -Filter "*.sal" | ForEach-Object {
            Write-Host "  - $($_.Name)" -ForegroundColor Cyan
        }
        return $false
    }
    
    Write-Host "✓ Файл модели найден: $file" -ForegroundColor Green
    return $true
}

# Определение команды SAL на основе метода
function Get-SALCommand {
    param([string]$method)
    
    switch ($method) {
        "mc" { return "sal-smc" }
        "bmc" { return "sal-inf-bmc" }
        "k-induction" { return "sal-inf-bmc" }
        "invariant" { return "sal-smc" }
        default { return "sal-smc" }
    }
}

# Основная функция верификации
function Invoke-SALVerification {
    param(
        [string]$modelFile,
        [string]$method,
        [string]$outputFile = ""
    )
    
    Write-Host "`n🚀 Запуск SAL верификации..." -ForegroundColor Magenta
    Write-Host "Модель: $modelFile" -ForegroundColor Cyan
    Write-Host "Метод: $method" -ForegroundColor Cyan
    
    # Определение команды и аргументов
    $command = Get-SALCommand -method $method
    $args = @()
    
    switch ($method) {
        "mc" { 
            $args = @("-v", "-d", "1", $modelFile)
        }
        "bmc" { 
            $args = @("-v", "-d", "10", $modelFile)
        }
        "k-induction" { 
            $args = @("-v", "-d", "10", "-i", $modelFile)
        }
        "invariant" { 
            $args = @("-v", "-d", "1", "--invariant", $modelFile)
        }
    }
    
    if ($Verbose) {
        Write-Host "Команда: $command $($args -join ' ')" -ForegroundColor Gray
    }
    
    # Запуск SAL
    try {
        if ($outputFile -and $outputFile -ne "") {
            Write-Host "Результаты будут сохранены в: $outputFile" -ForegroundColor Yellow
            & $command @args | Tee-Object -FilePath $outputFile
        } else {
            & $command @args
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "`n✅ SAL верификация завершена успешно!" -ForegroundColor Green
        } else {
            Write-Host "`n⚠️ SAL завершился с кодом: $LASTEXITCODE" -ForegroundColor Yellow
        }
    }
    catch {
        Write-Host "`n❌ Ошибка при запуске SAL: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Функция анализа результатов
function Analyze-SALResults {
    param([string]$outputFile)
    
    if (-not (Test-Path $outputFile)) {
        Write-Host "Файл результатов не найден для анализа" -ForegroundColor Yellow
        return
    }
    
    Write-Host "`n📊 Анализ результатов SAL..." -ForegroundColor Magenta
    
    $content = Get-Content $outputFile -Raw
    
    # Поиск результатов верификации
    if ($content -match "specification.*is false") {
        Write-Host "❌ Найдены нарушения спецификаций!" -ForegroundColor Red
    } elseif ($content -match "specification.*is true") {
        Write-Host "✅ Все спецификации выполняются" -ForegroundColor Green
    }
    
    # Поиск информации о состояниях
    if ($content -match "reachable states.*: (\d+)") {
        $states = $matches[1]
        Write-Host "📈 Достижимых состояний: $states" -ForegroundColor Cyan
    }
    
    # Поиск времени выполнения
    if ($content -match "execution time.*: ([\d.]+)") {
        $time = $matches[1]
        Write-Host "⏱️ Время выполнения: $time сек" -ForegroundColor Cyan
    }
    
    # Поиск информации о SMT решателе
    if ($content -match "SMT.*solver") {
        Write-Host "🔧 Использован SMT решатель" -ForegroundColor Cyan
    }
}

# Главная логика скрипта
function Main {
    if ($Help) {
        Show-Help
        return
    }
    
    Write-Host "🔍 SAL Symbolic Analysis Laboratory" -ForegroundColor Blue
    Write-Host "=====================================" -ForegroundColor Blue
    
    # Проверка SAL
    if (-not (Test-SAL)) {
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
    Invoke-SALVerification -modelFile $ModelFile -method $Method -outputFile $OutputFile
    
    # Анализ результатов
    if ($OutputFile -and $OutputFile -ne "") {
        Analyze-SALResults -outputFile $OutputFile
    }
    
    Write-Host "`n✨ Готово!" -ForegroundColor Green
}

# Запуск главной функции
Main
