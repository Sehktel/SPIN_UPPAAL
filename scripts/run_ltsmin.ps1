#!/usr/bin/env pwsh
# Скрипт для запуска LTSmin (Language-agnostic Tool)
# LTSmin - универсальный инструмент для анализа систем с помеченными переходами

param(
    [Parameter(Mandatory=$false)]
    [string]$ModelFile = "models/ltsmin/traffic_light.lts",
    
    [Parameter(Mandatory=$false)]
    [switch]$Help,
    
    [Parameter(Mandatory=$false)]
    [switch]$Verbose,
    
    [Parameter(Mandatory=$false)]
    [string]$OutputFile = "",
    
    [Parameter(Mandatory=$false)]
    [ValidateSet("safety", "liveness", "fairness", "all")]
    [string]$CheckType = "all"
)

# Функция вывода справки
function Show-Help {
    Write-Host @"
LTSmin Runner Script
====================

Использование:
    .\run_ltsmin.ps1 [-ModelFile <путь>] [-Help] [-Verbose] [-OutputFile <путь>] [-CheckType <тип>]

Параметры:
    -ModelFile     Путь к LTS файлу модели (по умолчанию: models/ltsmin/traffic_light.lts)
    -Help          Показать эту справку
    -Verbose       Подробный вывод
    -OutputFile    Файл для сохранения результатов
    -CheckType     Тип проверки: safety, liveness, fairness, all (по умолчанию: all)

Примеры:
    .\run_ltsmin.ps1
    .\run_ltsmin.ps1 -ModelFile "models/ltsmin/protocol_verification.lts"
    .\run_ltsmin.ps1 -Verbose -CheckType "safety" -OutputFile "results/ltsmin_output.txt"

LTSmin особенности:
    - Универсальный инструмент для множества языков
    - Гибридные алгоритмы (символический + явный)
    - Адаптивность и высокая производительность
    - Поддержка плагинов для различных форматов
"@
}

# Проверка наличия LTSmin
function Test-LTSmin {
    try {
        $version = ltsmin-verify -version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ LTSmin найден: $version" -ForegroundColor Green
            return $true
        }
    }
    catch {
        try {
            $version = ltsmin-verify.exe -version 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ LTSmin найден (ltsmin-verify.exe): $version" -ForegroundColor Green
                return $true
            }
        }
        catch {
            try {
                $version = ltsmin -version 2>&1
                if ($LASTEXITCODE -eq 0) {
                    Write-Host "✓ LTSmin найден (ltsmin): $version" -ForegroundColor Green
                    return $true
                }
            }
            catch {
                Write-Host "✗ LTSmin не найден в PATH" -ForegroundColor Red
                Write-Host "Установите LTSmin:" -ForegroundColor Yellow
                Write-Host "  Скачайте с: https://ltsmin.utwente.nl/" -ForegroundColor Cyan
                Write-Host "  Добавьте в PATH: C:\ltsmin\bin" -ForegroundColor Cyan
                return $false
            }
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
        Get-ChildItem "models/ltsmin/" -Filter "*.lts" | ForEach-Object {
            Write-Host "  - $($_.Name)" -ForegroundColor Cyan
        }
        return $false
    }
    
    Write-Host "✓ Файл модели найден: $file" -ForegroundColor Green
    return $true
}

# Определение команды LTSmin
function Get-LTSminCommand {
    try {
        if (Get-Command "ltsmin-verify" -ErrorAction SilentlyContinue) {
            return "ltsmin-verify"
        } elseif (Get-Command "ltsmin" -ErrorAction SilentlyContinue) {
            return "ltsmin"
        } else {
            return "ltsmin-verify.exe"
        }
    }
    catch {
        return "ltsmin-verify"
    }
}

# Определение аргументов LTSmin на основе типа проверки
function Get-LTSminArguments {
    param([string]$checkType)
    
    switch ($checkType) {
        "safety" { 
            return @("-safety", "-v", "-p", "4")
        }
        "liveness" { 
            return @("-liveness", "-v", "-p", "4")
        }
        "fairness" { 
            return @("-fairness", "-v", "-p", "4")
        }
        "all" { 
            return @("-all", "-v", "-p", "4")
        }
        default { 
            return @("-all", "-v", "-p", "4")
        }
    }
}

# Основная функция верификации
function Invoke-LTSminVerification {
    param(
        [string]$modelFile,
        [string]$checkType,
        [string]$outputFile = ""
    )
    
    Write-Host "`n🚀 Запуск LTSmin верификации..." -ForegroundColor Magenta
    Write-Host "Модель: $modelFile" -ForegroundColor Cyan
    Write-Host "Тип проверки: $checkType" -ForegroundColor Cyan
    
    # Определение команды и аргументов
    $command = Get-LTSminCommand
    $args = Get-LTSminArguments -checkType $checkType
    $args += $modelFile
    
    if ($Verbose) {
        Write-Host "Команда: $command $($args -join ' ')" -ForegroundColor Gray
    }
    
    # Запуск LTSmin
    try {
        if ($outputFile -and $outputFile -ne "") {
            Write-Host "Результаты будут сохранены в: $outputFile" -ForegroundColor Yellow
            & $command @args | Tee-Object -FilePath $outputFile
        } else {
            & $command @args
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "`n✅ LTSmin верификация завершена успешно!" -ForegroundColor Green
        } else {
            Write-Host "`n⚠️ LTSmin завершился с кодом: $LASTEXITCODE" -ForegroundColor Yellow
        }
    }
    catch {
        Write-Host "`n❌ Ошибка при запуске LTSmin: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Функция анализа результатов
function Analyze-LTSminResults {
    param([string]$outputFile)
    
    if (-not (Test-Path $outputFile)) {
        Write-Host "Файл результатов не найден для анализа" -ForegroundColor Yellow
        return
    }
    
    Write-Host "`n📊 Анализ результатов LTSmin..." -ForegroundColor Magenta
    
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
    
    # Поиск информации о гибридном подходе
    if ($content -match "hybrid.*algorithm") {
        Write-Host "🔧 Использован гибридный алгоритм" -ForegroundColor Cyan
    }
}

# Главная логика скрипта
function Main {
    if ($Help) {
        Show-Help
        return
    }
    
    Write-Host "🔍 LTSmin Language-agnostic Tool" -ForegroundColor Blue
    Write-Host "=================================" -ForegroundColor Blue
    
    # Проверка LTSmin
    if (-not (Test-LTSmin)) {
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
    Invoke-LTSminVerification -modelFile $ModelFile -checkType $CheckType -outputFile $OutputFile
    
    # Анализ результатов
    if ($OutputFile -and $OutputFile -ne "") {
        Analyze-LTSminResults -outputFile $OutputFile
    }
    
    Write-Host "`n✨ Готово!" -ForegroundColor Green
}

# Запуск главной функции
Main
