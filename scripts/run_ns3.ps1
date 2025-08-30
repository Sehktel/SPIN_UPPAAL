# PowerShell скрипт для запуска NS-3 симуляции промышленной сети
# Автор: Senior Developer
# Дата: 2024-12-19

param(
    [string]$ConfigFile = "config/ns3.conf",
    [string]$ModelFile = "models/ns3/industrial_network.py",
    [int]$SimulationTime = 100,
    [string]$OutputDir = "results/ns3",
    [switch]$Verbose,
    [switch]$Help
)

# Функция вывода справки
function Show-Help {
    Write-Host @"
NS-3 Industrial Network Simulator

Использование:
    .\run_ns3.ps1 [параметры]

Параметры:
    -ConfigFile <путь>     Путь к конфигурационному файлу (по умолчанию: config/ns3.conf)
    -ModelFile <путь>      Путь к модели сети (по умолчанию: models/ns3/industrial_network.py)
    -SimulationTime <сек>  Время симуляции в секундах (по умолчанию: 100)
    -OutputDir <путь>      Директория для результатов (по умолчанию: results/ns3)
    -Verbose               Подробный вывод
    -Help                  Показать эту справку

Примеры:
    .\run_ns3.ps1
    .\run_ns3.ps1 -SimulationTime 200 -Verbose
    .\run_ns3.ps1 -ConfigFile "custom_config.conf" -OutputDir "custom_results"

"@
}

# Проверка параметра справки
if ($Help) {
    Show-Help
    exit 0
}

# Проверка наличия NS-3
function Test-NS3Installation {
    Write-Host "🔍 Проверка установки NS-3..." -ForegroundColor Yellow
    
    # Проверка переменной окружения NS3_ROOT
    if ($env:NS3_ROOT) {
        Write-Host "✅ NS3_ROOT найден: $env:NS3_ROOT" -ForegroundColor Green
        return $true
    }
    
    # Проверка стандартных путей установки
    $ns3Paths = @(
        "C:\ns-3.40",
        "C:\ns-3.39",
        "C:\ns-3.38",
        "$env:USERPROFILE\ns-3.40",
        "$env:USERPROFILE\ns-3.39"
    )
    
    foreach ($path in $ns3Paths) {
        if (Test-Path $path) {
            Write-Host "✅ NS-3 найден в: $path" -ForegroundColor Green
            $env:NS3_ROOT = $path
            return $true
        }
    }
    
    Write-Host "❌ NS-3 не найден. Установите NS-3 или установите переменную NS3_ROOT" -ForegroundColor Red
    return $false
}

# Проверка зависимостей
function Test-NS3Dependencies {
    Write-Host "🔍 Проверка зависимостей NS-3..." -ForegroundColor Yellow
    
    # Проверка Python
    try {
        $pythonVersion = python --version 2>&1
        Write-Host "✅ Python найден: $pythonVersion" -ForegroundColor Green
    }
    catch {
        Write-Host "❌ Python не найден. Установите Python 3.7+" -ForegroundColor Red
        return $false
    }
    
    # Проверка pip
    try {
        $pipVersion = pip --version 2>&1
        Write-Host "✅ pip найден: $pipVersion" -ForegroundColor Green
    }
    catch {
        Write-Host "❌ pip не найден. Установите pip" -ForegroundColor Red
        return $false
    }
    
    return $true
}

# Установка зависимостей Python
function Install-PythonDependencies {
    Write-Host "📦 Установка зависимостей Python..." -ForegroundColor Yellow
    
    $dependencies = @(
        "numpy",
        "matplotlib",
        "scipy",
        "pandas"
    )
    
    foreach ($dep in $dependencies) {
        try {
            Write-Host "Установка $dep..." -ForegroundColor Cyan
            pip install $dep --quiet
            Write-Host "✅ $dep установлен" -ForegroundColor Green
        }
        catch {
            Write-Host "⚠️ Не удалось установить $dep" -ForegroundColor Yellow
        }
    }
}

# Проверка конфигурационного файла
function Test-ConfigFile {
    param([string]$ConfigPath)
    
    if (-not (Test-Path $ConfigPath)) {
        Write-Host "❌ Конфигурационный файл не найден: $ConfigPath" -ForegroundColor Red
        return $false
    }
    
    Write-Host "✅ Конфигурационный файл найден: $ConfigPath" -ForegroundColor Green
    return $true
}

# Проверка модели
function Test-ModelFile {
    param([string]$ModelPath)
    
    if (-not (Test-Path $ModelPath)) {
        Write-Host "❌ Файл модели не найден: $ModelPath" -ForegroundColor Red
        return $false
    }
    
    Write-Host "✅ Файл модели найден: $ModelPath" -ForegroundColor Green
    return $true
}

# Создание директории результатов
function New-OutputDirectory {
    param([string]$OutputPath)
    
    if (-not (Test-Path $OutputPath)) {
        New-Item -ItemType Directory -Path $OutputPath -Force | Out-Null
        Write-Host "✅ Создана директория результатов: $OutputPath" -ForegroundColor Green
    }
    else {
        Write-Host "✅ Директория результатов существует: $OutputPath" -ForegroundColor Green
    }
}

# Запуск симуляции NS-3
function Start-NS3Simulation {
    param(
        [string]$ModelPath,
        [string]$OutputPath,
        [int]$SimTime
    )
    
    Write-Host "🚀 Запуск симуляции NS-3..." -ForegroundColor Green
    Write-Host "Модель: $ModelPath" -ForegroundColor Cyan
    Write-Host "Время симуляции: $SimTime секунд" -ForegroundColor Cyan
    Write-Host "Результаты: $OutputPath" -ForegroundColor Cyan
    
    # Переход в директорию результатов
    Push-Location $OutputPath
    
    try {
        # Запуск симуляции
        Write-Host "⏳ Выполнение симуляции..." -ForegroundColor Yellow
        
        if ($Verbose) {
            python $ModelPath
        }
        else {
            python $ModelPath 2>&1 | Out-Null
        }
        
        Write-Host "✅ Симуляция завершена успешно!" -ForegroundColor Green
        
        # Проверка результатов
        $results = Get-ChildItem -Path "." -Filter "*.xml" | Sort-Object LastWriteTime -Descending
        if ($results) {
            Write-Host "📊 Результаты симуляции:" -ForegroundColor Green
            foreach ($result in $results) {
                Write-Host "  - $($result.Name) ($($result.Length) байт)" -ForegroundColor Cyan
            }
        }
    }
    catch {
        Write-Host "❌ Ошибка при выполнении симуляции: $($_.Exception.Message)" -ForegroundColor Red
        return $false
    }
    finally {
        Pop-Location
    }
    
    return $true
}

# Анализ результатов
function Analyze-NS3Results {
    param([string]$OutputPath)
    
    Write-Host "📈 Анализ результатов симуляции..." -ForegroundColor Yellow
    
    $xmlFiles = Get-ChildItem -Path $OutputPath -Filter "*.xml"
    
    if (-not $xmlFiles) {
        Write-Host "⚠️ Файлы результатов не найдены" -ForegroundColor Yellow
        return
    }
    
    foreach ($xmlFile in $xmlFiles) {
        Write-Host "📄 Анализ файла: $($xmlFile.Name)" -ForegroundColor Cyan
        
        try {
            # Простой анализ XML файла
            $xml = [xml](Get-Content $xmlFile.FullName)
            
            # Поиск статистики потоков
            $flows = $xml.SelectNodes("//Flow")
            if ($flows) {
                Write-Host "  Потоков: $($flows.Count)" -ForegroundColor Green
                
                foreach ($flow in $flows[0..2]) { # Показываем первые 3 потока
                    $src = $flow.Source
                    $dst = $flow.Destination
                    $packets = $flow.Packets
                    Write-Host "    $src -> $dst : $packets пакетов" -ForegroundColor White
                }
            }
        }
        catch {
            Write-Host "  ⚠️ Не удалось проанализировать XML" -ForegroundColor Yellow
        }
    }
}

# Основная функция
function Main {
    Write-Host "🏭 NS-3 Industrial Network Simulator" -ForegroundColor Magenta
    Write-Host "=====================================" -ForegroundColor Magenta
    
    # Проверка установки NS-3
    if (-not (Test-NS3Installation)) {
        Write-Host "❌ Не удалось найти NS-3. Завершение работы." -ForegroundColor Red
        exit 1
    }
    
    # Проверка зависимостей
    if (-not (Test-NS3Dependencies)) {
        Write-Host "❌ Не удалось проверить зависимости. Завершение работы." -ForegroundColor Red
        exit 1
    }
    
    # Установка зависимостей Python
    Install-PythonDependencies
    
    # Проверка файлов
    if (-not (Test-ConfigFile $ConfigFile)) {
        Write-Host "❌ Ошибка конфигурации. Завершение работы." -ForegroundColor Red
        exit 1
    }
    
    if (-not (Test-ModelFile $ModelFile)) {
        Write-Host "❌ Ошибка модели. Завершение работы." -ForegroundColor Red
        exit 1
    }
    
    # Создание директории результатов
    New-OutputDirectory $OutputDir
    
    # Запуск симуляции
    if (Start-NS3Simulation -ModelPath $ModelFile -OutputPath $OutputDir -SimTime $SimulationTime) {
        # Анализ результатов
        Analyze-NS3Results $OutputDir
        
        Write-Host "🎉 Симуляция NS-3 завершена успешно!" -ForegroundColor Green
        Write-Host "Результаты сохранены в: $OutputDir" -ForegroundColor Cyan
    }
    else {
        Write-Host "❌ Симуляция NS-3 завершилась с ошибкой." -ForegroundColor Red
        exit 1
    }
}

# Запуск основной функции
if ($MyInvocation.InvocationName -ne ".") {
    Main
}

