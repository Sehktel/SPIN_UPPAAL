#!/usr/bin/env pwsh
# Скрипт для запуска BANDERA (Java Model Checker)
# BANDERA специализируется на верификации Java программ

param(
    [Parameter(Mandatory=$false)]
    [string]$ModelFile = "models/bandera/TrafficLight.java",
    
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
BANDERA Runner Script
=====================

Использование:
    .\run_bandera.ps1 [-ModelFile <путь>] [-Help] [-Verbose] [-OutputFile <путь>] [-CheckType <тип>]

Параметры:
    -ModelFile     Путь к Java файлу модели (по умолчанию: models/bandera/TrafficLight.java)
    -Help          Показать эту справку
    -Verbose       Подробный вывод
    -OutputFile    Файл для сохранения результатов
    -CheckType     Тип проверки: safety, liveness, deadlock, all (по умолчанию: all)

Примеры:
    .\run_bandera.ps1
    .\run_bandera.ps1 -ModelFile "models/bandera/concurrent_java.java"
    .\run_bandera.ps1 -Verbose -CheckType "safety" -OutputFile "results/bandera_output.txt"

BANDERA особенности:
    - Специализация на Java программах
    - Абстракция и специализация
    - Интеграция с Java экосистемой
    - Подходит для веб-приложений и Java систем
"@
}

# Проверка наличия Java
function Test-Java {
    try {
        $version = java -version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ Java найден: $version" -ForegroundColor Green
            return $true
        }
    }
    catch {
        Write-Host "✗ Java не найден в PATH" -ForegroundColor Red
        Write-Host "Установите Java:" -ForegroundColor Yellow
        Write-Host "  winget install Oracle.Java" -ForegroundColor Cyan
        Write-Host "  или скачайте с: https://www.oracle.com/java/" -ForegroundColor Cyan
        return $false
    }
    return $false
}

# Проверка наличия BANDERA
function Test-BANDERA {
    try {
        $version = bandera -version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ BANDERA найден: $version" -ForegroundColor Green
            return $true
        }
    }
    catch {
        try {
            $version = bandera.jar -version 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ BANDERA найден (JAR): $version" -ForegroundColor Green
                return $true
            }
        }
        catch {
            Write-Host "✗ BANDERA не найден в PATH" -ForegroundColor Red
            Write-Host "Установите BANDERA:" -ForegroundColor Yellow
            Write-Host "  Скачайте с: http://bandera.projects.cis.ksu.edu/" -ForegroundColor Cyan
            Write-Host "  Добавьте в PATH: C:\bandera\bin" -ForegroundColor Cyan
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
        Get-ChildItem "models/bandera/" -Filter "*.java" | ForEach-Object {
            Write-Host "  - $($_.Name)" -ForegroundColor Cyan
        }
        return $false
    }
    
    Write-Host "✓ Файл модели найден: $file" -ForegroundColor Green
    return $true
}

# Компиляция Java файла
function Compile-JavaFile {
    param([string]$javaFile)
    
    Write-Host "🔨 Компиляция Java файла..." -ForegroundColor Yellow
    
    try {
        $className = [System.IO.Path]::GetFileNameWithoutExtension($javaFile)
        $classFile = "$className.class"
        
        # Удаление старого .class файла если существует
        if (Test-Path $classFile) {
            Remove-Item $classFile -Force
        }
        
        # Компиляция
        javac $javaFile
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ Компиляция успешна: $classFile" -ForegroundColor Green
            return $true
        } else {
            Write-Host "✗ Ошибка компиляции" -ForegroundColor Red
            return $false
        }
    }
    catch {
        Write-Host "✗ Ошибка при компиляции: $($_.Exception.Message)" -ForegroundColor Red
        return $false
    }
}

# Определение команды BANDERA
function Get-BANDERACommand {
    try {
        if (Get-Command "bandera" -ErrorAction SilentlyContinue) {
            return "bandera"
        } elseif (Get-Command "bandera.jar" -ErrorAction SilentlyContinue) {
            return "java -jar bandera.jar"
        } else {
            return "bandera"
        }
    }
    catch {
        return "bandera"
    }
}

# Основная функция верификации
function Invoke-BANDERAVerification {
    param(
        [string]$modelFile,
        [string]$checkType,
        [string]$outputFile = ""
    )
    
    Write-Host "`n🚀 Запуск BANDERA верификации..." -ForegroundColor Magenta
    Write-Host "Модель: $modelFile" -ForegroundColor Cyan
    Write-Host "Тип проверки: $checkType" -ForegroundColor Cyan
    
    # Определение команды и аргументов
    $command = Get-BANDERACommand
    $args = @()
    
    switch ($checkType) {
        "safety" { 
            $args = @("-safety", "-verbose", $modelFile)
        }
        "liveness" { 
            $args = @("-liveness", "-verbose", $modelFile)
        }
        "deadlock" { 
            $args = @("-deadlock", "-verbose", $modelFile)
        }
        "all" { 
            $args = @("-all", "-verbose", $modelFile)
        }
        default { 
            $args = @("-all", "-verbose", $modelFile)
        }
    }
    
    if ($Verbose) {
        Write-Host "Команда: $command $($args -join ' ')" -ForegroundColor Gray
    }
    
    # Запуск BANDERA
    try {
        if ($outputFile -and $outputFile -ne "") {
            Write-Host "Результаты будут сохранены в: $outputFile" -ForegroundColor Yellow
            & $command @args | Tee-Object -FilePath $outputFile
        } else {
            & $command @args
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "`n✅ BANDERA верификация завершена успешно!" -ForegroundColor Green
        } else {
            Write-Host "`n⚠️ BANDERA завершился с кодом: $LASTEXITCODE" -ForegroundColor Yellow
        }
    }
    catch {
        Write-Host "`n❌ Ошибка при запуске BANDERA: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Функция анализа результатов
function Analyze-BANDERAResults {
    param([string]$outputFile)
    
    if (-not (Test-Path $outputFile)) {
        Write-Host "Файл результатов не найден для анализа" -ForegroundColor Yellow
        return
    }
    
    Write-Host "`n📊 Анализ результатов BANDERA..." -ForegroundColor Magenta
    
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
    
    # Поиск информации о Java
    if ($content -match "Java.*verification") {
        Write-Host "🔧 Использована Java верификация" -ForegroundColor Cyan
    }
}

# Главная логика скрипта
function Main {
    if ($Help) {
        Show-Help
        return
    }
    
    Write-Host "🔍 BANDERA Java Model Checker" -ForegroundColor Blue
    Write-Host "=============================" -ForegroundColor Blue
    
    # Проверка Java
    if (-not (Test-Java)) {
        return
    }
    
    # Проверка BANDERA
    if (-not (Test-BANDERA)) {
        return
    }
    
    # Проверка файла модели
    if (-not (Test-ModelFile $ModelFile)) {
        return
    }
    
    # Компиляция Java файла
    if (-not (Compile-JavaFile $ModelFile)) {
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
    Invoke-BANDERAVerification -modelFile $ModelFile -checkType $CheckType -outputFile $OutputFile
    
    # Анализ результатов
    if ($OutputFile -and $OutputFile -ne "") {
        Analyze-BANDERAResults -outputFile $OutputFile
    }
    
    Write-Host "`n✨ Готово!" -ForegroundColor Green
}

# Запуск главной функции
Main
