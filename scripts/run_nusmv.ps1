#!/usr/bin/env pwsh
# Скрипт для запуска NuSMV (Symbolic Model Checker)
# NuSMV использует BDD для эффективной работы с большими пространствами состояний

param(
    [Parameter(Mandatory=$false)]
    [string]$ModelFile = "models/nusmv/traffic_light.smv",
    
    [Parameter(Mandatory=$false)]
    [switch]$Help,
    
    [Parameter(Mandatory=$false)]
    [switch]$Verbose,
    
    [Parameter(Mandatory=$false)]
    [string]$OutputFile = ""
)

# Функция вывода справки
function Show-Help {
    Write-Host @"
NuSMV Runner Script
===================

Использование:
    .\run_nusmv.ps1 [-ModelFile <путь>] [-Help] [-Verbose] [-OutputFile <путь>]

Параметры:
    -ModelFile     Путь к SMV файлу модели (по умолчанию: models/nusmv/traffic_light.smv)
    -Help          Показать эту справку
    -Verbose       Подробный вывод
    -OutputFile    Файл для сохранения результатов

Примеры:
    .\run_nusmv.ps1
    .\run_nusmv.ps1 -ModelFile "models/nusmv/plc_system.smv"
    .\run_nusmv.ps1 -Verbose -OutputFile "results/nusmv_output.txt"

NuSMV особенности:
    - Символический анализ с использованием BDD
    - Поддержка LTL и CTL спецификаций
    - Эффективен для систем с регулярной структурой
    - Высокая производительность для больших моделей
"@
}

# Проверка наличия NuSMV
function Test-NuSMV {
    try {
        $version = nusmv -version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ NuSMV найден: $version" -ForegroundColor Green
            return $true
        }
    }
    catch {
        Write-Host "✗ NuSMV не найден в PATH" -ForegroundColor Red
        Write-Host "Установите NuSMV:" -ForegroundColor Yellow
        Write-Host "  winget install nusmv" -ForegroundColor Cyan
        Write-Host "  или скачайте с: http://nusmv.fbk.eu/" -ForegroundColor Cyan
        return $false
    }
    return $false
}

# Проверка существования файла модели
function Test-ModelFile {
    param([string]$file)
    
    if (-not (Test-Path $file)) {
        Write-Host "✗ Файл модели не найден: $file" -ForegroundColor Red
        Write-Host "Доступные модели:" -ForegroundColor Yellow
        Get-ChildItem "models/nusmv/" -Filter "*.smv" | ForEach-Object {
            Write-Host "  - $($_.Name)" -ForegroundColor Cyan
        }
        return $false
    }
    
    Write-Host "✓ Файл модели найден: $file" -ForegroundColor Green
    return $true
}

# Основная функция верификации
function Invoke-NuSMVVerification {
    param(
        [string]$modelFile,
        [string]$outputFile = ""
    )
    
    Write-Host "`n🚀 Запуск NuSMV верификации..." -ForegroundColor Magenta
    Write-Host "Модель: $modelFile" -ForegroundColor Cyan
    
    # Команда для верификации
    $command = "nusmv"
    $args = @("-int", "-bmc", "-bmc_length", "20", $modelFile)
    
    if ($Verbose) {
        Write-Host "Команда: $command $($args -join ' ')" -ForegroundColor Gray
    }
    
    # Запуск NuSMV
    try {
        if ($outputFile -and $outputFile -ne "") {
            Write-Host "Результаты будут сохранены в: $outputFile" -ForegroundColor Yellow
            & $command @args | Tee-Object -FilePath $outputFile
        } else {
            & $command @args
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "`n✅ NuSMV верификация завершена успешно!" -ForegroundColor Green
        } else {
            Write-Host "`n⚠️ NuSMV завершился с кодом: $LASTEXITCODE" -ForegroundColor Yellow
        }
    }
    catch {
        Write-Host "`n❌ Ошибка при запуске NuSMV: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Функция анализа результатов
function Analyze-NuSMVResults {
    param([string]$outputFile)
    
    if (-not (Test-Path $outputFile)) {
        Write-Host "Файл результатов не найден для анализа" -ForegroundColor Yellow
        return
    }
    
    Write-Host "`n📊 Анализ результатов NuSMV..." -ForegroundColor Magenta
    
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
}

# Главная логика скрипта
function Main {
    if ($Help) {
        Show-Help
        return
    }
    
    Write-Host "🔍 NuSMV Symbolic Model Checker" -ForegroundColor Blue
    Write-Host "=================================" -ForegroundColor Blue
    
    # Проверка NuSMV
    if (-not (Test-NuSMV)) {
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
    Invoke-NuSMVVerification -modelFile $ModelFile -outputFile $OutputFile
    
    # Анализ результатов
    if ($OutputFile -and $OutputFile -ne "") {
        Analyze-NuSMVResults -outputFile $OutputFile
    }
    
    Write-Host "`n✨ Готово!" -ForegroundColor Green
}

# Запуск главной функции
Main
