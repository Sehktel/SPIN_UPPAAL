#!/usr/bin/env pwsh
# Скрипт для запуска ProB (B Method Tool)
# ProB основан на B методологии и теории множеств

param(
    [Parameter(Mandatory=$false)]
    [string]$ModelFile = "models/prob/traffic_light.mch",
    
    [Parameter(Mandatory=$false)]
    [switch]$Help,
    
    [Parameter(Mandatory=$false)]
    [switch]$Verbose,
    
    [Parameter(Mandatory=$false)]
    [string]$OutputFile = "",
    
    [Parameter(Mandatory=$false)]
    [ValidateSet("invariant", "deadlock", "assertion", "all")]
    [string]$CheckType = "all"
)

# Функция вывода справки
function Show-Help {
    Write-Host @"
ProB Runner Script
==================

Использование:
    .\run_prob.ps1 [-ModelFile <путь>] [-Help] [-Verbose] [-OutputFile <путь>] [-CheckType <тип>]

Параметры:
    -ModelFile     Путь к MCH файлу модели (по умолчанию: models/prob/traffic_light.mch)
    -Help          Показать эту справку
    -Verbose       Подробный вывод
    -OutputFile    Файл для сохранения результатов
    -CheckType     Тип проверки: invariant, deadlock, assertion, all (по умолчанию: all)

Примеры:
    .\run_prob.ps1
    .\run_prob.ps1 -ModelFile "models/prob/formal_specification.mch"
    .\run_prob.ps1 -Verbose -CheckType "invariant" -OutputFile "results/prob_output.txt"

ProB особенности:
    - B методология и теория множеств
    - Формальные методы и математическая строгость
    - Подходит для критически важных систем
    - Интерактивный режим верификации
"@
}

# Проверка наличия ProB
function Test-ProB {
    try {
        $version = prob -version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ ProB найден: $version" -ForegroundColor Green
            return $true
        }
    }
    catch {
        try {
            $version = prob.exe -version 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ ProB найден (prob.exe): $version" -ForegroundColor Green
                return $true
            }
        }
        catch {
            try {
                $version = probcli -version 2>&1
                if ($LASTEXITCODE -eq 0) {
                    Write-Host "✓ ProB найден (probcli): $version" -ForegroundColor Green
                    return $true
                }
            }
            catch {
                Write-Host "✗ ProB не найден в PATH" -ForegroundColor Red
                Write-Host "Установите ProB:" -ForegroundColor Yellow
                Write-Host "  Скачайте с: https://www3.hhu.de/stups/prob/" -ForegroundColor Cyan
                Write-Host "  Добавьте в PATH: C:\proB\bin" -ForegroundColor Cyan
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
        Get-ChildItem "models/prob/" -Filter "*.mch" | ForEach-Object {
            Write-Host "  - $($_.Name)" -ForegroundColor Cyan
        }
        return $false
    }
    
    Write-Host "✓ Файл модели найден: $file" -ForegroundColor Green
    return $true
}

# Определение команды ProB
function Get-ProBCommand {
    try {
        if (Get-Command "probcli" -ErrorAction SilentlyContinue) {
            return "probcli"
        } elseif (Get-Command "prob" -ErrorAction SilentlyContinue) {
            return "prob"
        } else {
            return "prob.exe"
        }
    }
    catch {
        return "prob"
    }
}

# Определение аргументов ProB на основе типа проверки
function Get-ProBArguments {
    param([string]$checkType)
    
    switch ($checkType) {
        "invariant" { 
            return @("-inv", "-p", "-mc", "1000")
        }
        "deadlock" { 
            return @("-deadlock", "-p", "-mc", "1000")
        }
        "assertion" { 
            return @("-assert", "-p", "-mc", "1000")
        }
        "all" { 
            return @("-inv", "-deadlock", "-assert", "-p", "-mc", "1000")
        }
        default { 
            return @("-inv", "-deadlock", "-assert", "-p", "-mc", "1000")
        }
    }
}

# Основная функция верификации
function Invoke-ProBVerification {
    param(
        [string]$modelFile,
        [string]$checkType,
        [string]$outputFile = ""
    )
    
    Write-Host "`n🚀 Запуск ProB верификации..." -ForegroundColor Magenta
    Write-Host "Модель: $modelFile" -ForegroundColor Cyan
    Write-Host "Тип проверки: $checkType" -ForegroundColor Cyan
    
    # Определение команды и аргументов
    $command = Get-ProBCommand
    $args = Get-ProBArguments -checkType $checkType
    $args += $modelFile
    
    if ($Verbose) {
        Write-Host "Команда: $command $($args -join ' ')" -ForegroundColor Gray
    }
    
    # Запуск ProB
    try {
        if ($outputFile -and $outputFile -ne "") {
            Write-Host "Результаты будут сохранены в: $outputFile" -ForegroundColor Yellow
            & $command @args | Tee-Object -FilePath $outputFile
        } else {
            & $command @args
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "`n✅ ProB верификация завершена успешно!" -ForegroundColor Green
        } else {
            Write-Host "`n⚠️ ProB завершился с кодом: $LASTEXITCODE" -ForegroundColor Yellow
        }
    }
    catch {
        Write-Host "`n❌ Ошибка при запуске ProB: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Функция анализа результатов
function Analyze-ProBResults {
    param([string]$outputFile)
    
    if (-not (Test-Path $outputFile)) {
        Write-Host "Файл результатов не найден для анализа" -ForegroundColor Yellow
        return
    }
    
    Write-Host "`n📊 Анализ результатов ProB..." -ForegroundColor Magenta
    
    $content = Get-Content $outputFile -Raw
    
    # Поиск результатов верификации
    if ($content -match "invariant.*violated") {
        Write-Host "❌ Найдены нарушения инвариантов!" -ForegroundColor Red
    } elseif ($content -match "invariant.*preserved") {
        Write-Host "✅ Инварианты сохранены" -ForegroundColor Green
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
    
    # Поиск информации о B методологии
    if ($content -match "B.*method") {
        Write-Host "🔧 Использована B методология" -ForegroundColor Cyan
    }
}

# Главная логика скрипта
function Main {
    if ($Help) {
        Show-Help
        return
    }
    
    Write-Host "🔍 ProB B Method Tool" -ForegroundColor Blue
    Write-Host "=====================" -ForegroundColor Blue
    
    # Проверка ProB
    if (-not (Test-ProB)) {
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
    Invoke-ProBVerification -modelFile $ModelFile -checkType $CheckType -outputFile $OutputFile
    
    # Анализ результатов
    if ($OutputFile -and $OutputFile -ne "") {
        Analyze-ProBResults -outputFile $OutputFile
    }
    
    Write-Host "`n✨ Готово!" -ForegroundColor Green
}

# Запуск главной функции
Main
