#!/usr/bin/env pwsh
# Скрипт для запуска PAT (Process Algebra Tool)
# PAT основан на CSP (Communicating Sequential Processes) и процессной алгебре

param(
    [Parameter(Mandatory=$false)]
    [string]$ModelFile = "models/pat/traffic_light.csp",
    
    [Parameter(Mandatory=$false)]
    [switch]$Help,
    
    [Parameter(Mandatory=$false)]
    [switch]$Verbose,
    
    [Parameter(Mandatory=$false)]
    [string]$OutputFile = "",
    
    [Parameter(Mandatory=$false)]
    [ValidateSet("refinement", "deadlock", "divergence", "assertion")]
    [string]$CheckType = "refinement"
)

# Функция вывода справки
function Show-Help {
    Write-Host @"
PAT Runner Script
=================

Использование:
    .\run_pat.ps1 [-ModelFile <путь>] [-Help] [-Verbose] [-OutputFile <путь>] [-CheckType <тип>]

Параметры:
    -ModelFile     Путь к CSP файлу модели (по умолчанию: models/pat/traffic_light.csp)
    -Help          Показать эту справку
    -Verbose       Подробный вывод
    -OutputFile    Файл для сохранения результатов
    -CheckType     Тип проверки: refinement, deadlock, divergence, assertion (по умолчанию: refinement)

Примеры:
    .\run_pat.ps1
    .\run_pat.ps1 -ModelFile "models/pat/communication_protocol.csp"
    .\run_pat.ps1 -Verbose -CheckType "deadlock" -OutputFile "results/pat_output.txt"

PAT особенности:
    - Процессная алгебра CSP (Communicating Sequential Processes)
    - Композиционное моделирование
    - Эффективен для протоколов связи и конкурентных систем
    - Поддержка различных типов проверок
"@
}

# Проверка наличия PAT
function Test-PAT {
    try {
        $version = pat -version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ PAT найден: $version" -ForegroundColor Green
            return $true
        }
    }
    catch {
        try {
            $version = pat.exe -version 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ PAT найден (pat.exe): $version" -ForegroundColor Green
                return $true
            }
        }
        catch {
            Write-Host "✗ PAT не найден в PATH" -ForegroundColor Red
            Write-Host "Установите PAT:" -ForegroundColor Yellow
            Write-Host "  Скачайте с: http://pat.comp.nus.edu.sg/" -ForegroundColor Cyan
            Write-Host "  Добавьте в PATH: C:\pat\bin" -ForegroundColor Cyan
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
        Get-ChildItem "models/pat/" -Filter "*.csp" | ForEach-Object {
            Write-Host "  - $($_.Name)" -ForegroundColor Cyan
        }
        return $false
    }
    
    Write-Host "✓ Файл модели найден: $file" -ForegroundColor Green
    return $true
}

# Определение аргументов PAT на основе типа проверки
function Get-PATArguments {
    param([string]$checkType)
    
    switch ($checkType) {
        "refinement" { 
            return @("-refinement", "-depth", "10")
        }
        "deadlock" { 
            return @("-deadlock", "-depth", "10")
        }
        "divergence" { 
            return @("-divergence", "-depth", "10")
        }
        "assertion" { 
            return @("-assertion", "-depth", "10")
        }
        default { 
            return @("-refinement", "-depth", "10")
        }
    }
}

# Основная функция верификации
function Invoke-PATVerification {
    param(
        [string]$modelFile,
        [string]$checkType,
        [string]$outputFile = ""
    )
    
    Write-Host "`n🚀 Запуск PAT верификации..." -ForegroundColor Magenta
    Write-Host "Модель: $modelFile" -ForegroundColor Cyan
    Write-Host "Тип проверки: $checkType" -ForegroundColor Cyan
    
    # Определение команды и аргументов
    $command = "pat"
    $args = Get-PATArguments -checkType $checkType
    $args += $modelFile
    
    if ($Verbose) {
        Write-Host "Команда: $command $($args -join ' ')" -ForegroundColor Gray
    }
    
    # Запуск PAT
    try {
        if ($outputFile -and $outputFile -ne "") {
            Write-Host "Результаты будут сохранены в: $outputFile" -ForegroundColor Yellow
            & $command @args | Tee-Object -FilePath $outputFile
        } else {
            & $command @args
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "`n✅ PAT верификация завершена успешно!" -ForegroundColor Green
        } else {
            Write-Host "`n⚠️ PAT завершился с кодом: $LASTEXITCODE" -ForegroundColor Yellow
        }
    }
    catch {
        Write-Host "`n❌ Ошибка при запуске PAT: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Функция анализа результатов
function Analyze-PATResults {
    param([string]$outputFile)
    
    if (-not (Test-Path $outputFile)) {
        Write-Host "Файл результатов не найден для анализа" -ForegroundColor Yellow
        return
    }
    
    Write-Host "`n📊 Анализ результатов PAT..." -ForegroundColor Magenta
    
    $content = Get-Content $outputFile -Raw
    
    # Поиск результатов верификации
    if ($content -match "refinement.*false") {
        Write-Host "❌ Найдены нарушения уточнения!" -ForegroundColor Red
    } elseif ($content -match "refinement.*true") {
        Write-Host "✅ Уточнение выполняется" -ForegroundColor Green
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
    
    # Поиск информации о процессах
    if ($content -match "processes.*: (\d+)") {
        $processes = $matches[1]
        Write-Host "🔄 Процессов: $processes" -ForegroundColor Cyan
    }
}

# Главная логика скрипта
function Main {
    if ($Help) {
        Show-Help
        return
    }
    
    Write-Host "🔍 PAT Process Algebra Tool" -ForegroundColor Blue
    Write-Host "============================" -ForegroundColor Blue
    
    # Проверка PAT
    if (-not (Test-PAT)) {
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
    Invoke-PATVerification -modelFile $ModelFile -checkType $CheckType -outputFile $OutputFile
    
    # Анализ результатов
    if ($OutputFile -and $OutputFile -ne "") {
        Analyze-PATResults -outputFile $OutputFile
    }
    
    Write-Host "`n✨ Готово!" -ForegroundColor Green
}

# Запуск главной функции
Main
