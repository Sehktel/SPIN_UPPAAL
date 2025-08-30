# PowerShell скрипт для запуска OMNeT++ симуляции промышленной сети
# Автор: Senior Developer
# Дата: 2024-12-19

param(
    [string]$ConfigFile = "config/omnetpp.conf",
    [string]$ModelFile = "models/omnetpp/IndustrialNetwork.ned",
    [int]$SimulationTime = 100,
    [string]$OutputDir = "results/omnetpp",
    [switch]$Verbose,
    [switch]$Help,
    [switch]$Gui
)

# Функция вывода справки
function Show-Help {
    Write-Host @"
OMNeT++ Industrial Network Simulator

Использование:
    .\run_omnetpp.ps1 [параметры]

Параметры:
    -ConfigFile <путь>     Путь к конфигурационному файлу (по умолчанию: config/omnetpp.conf)
    -ModelFile <путь>      Путь к модели сети (по умолчанию: models/omnetpp/IndustrialNetwork.ned)
    -SimulationTime <сек>  Время симуляции в секундах (по умолчанию: 100)
    -OutputDir <путь>      Директория для результатов (по умолчанию: results/omnetpp)
    -Verbose               Подробный вывод
    -Gui                   Запуск с графическим интерфейсом
    -Help                  Показать эту справку

Примеры:
    .\run_omnetpp.ps1
    .\run_omnetpp.ps1 -SimulationTime 200 -Verbose
    .\run_omnetpp.ps1 -Gui -ConfigFile "custom_config.conf"

"@
}

# Проверка параметра справки
if ($Help) {
    Show-Help
    exit 0
}

# Проверка наличия OMNeT++
function Test-OMNeTInstallation {
    Write-Host "🔍 Проверка установки OMNeT++..." -ForegroundColor Yellow
    
    # Проверка переменной окружения OMNETPP_ROOT
    if ($env:OMNETPP_ROOT) {
        Write-Host "✅ OMNETPP_ROOT найден: $env:OMNETPP_ROOT" -ForegroundColor Green
        return $true
    }
    
    # Проверка стандартных путей установки
    $omnetPaths = @(
        "C:\omnetpp-6.0",
        "C:\omnetpp-5.7",
        "C:\omnetpp-5.6",
        "$env:USERPROFILE\omnetpp-6.0",
        "$env:USERPROFILE\omnetpp-5.7"
    )
    
    foreach ($path in $omnetPaths) {
        if (Test-Path $path) {
            Write-Host "✅ OMNeT++ найден в: $path" -ForegroundColor Green
            $env:OMNETPP_ROOT = $path
            return $true
        }
    }
    
    Write-Host "❌ OMNeT++ не найден. Установите OMNeT++ или установите переменную OMNETPP_ROOT" -ForegroundColor Red
    return $false
}

# Проверка зависимостей
function Test-OMNeTDependencies {
    Write-Host "🔍 Проверка зависимостей OMNeT++..." -ForegroundColor Yellow
    
    # Проверка Java
    try {
        $javaVersion = java -version 2>&1
        Write-Host "✅ Java найден: $javaVersion" -ForegroundColor Green
    }
    catch {
        Write-Host "❌ Java не найден. Установите Java 8+" -ForegroundColor Red
        return $false
    }
    
    # Проверка Qt (для GUI)
    if ($Gui) {
        try {
            $qtVersion = qmake -query QT_VERSION 2>&1
            Write-Host "✅ Qt найден: $qtVersion" -ForegroundColor Green
        }
        catch {
            Write-Host "⚠️ Qt не найден. GUI может не работать" -ForegroundColor Yellow
        }
    }
    
    return $true
}

# Настройка переменных окружения OMNeT++
function Set-OMNeTEnvironment {
    Write-Host "🔧 Настройка переменных окружения OMNeT++..." -ForegroundColor Yellow
    
    if ($env:OMNETPP_ROOT) {
        $omnetRoot = $env:OMNETPP_ROOT
        
        # Добавление путей в PATH
        $paths = @(
            "$omnetRoot\bin",
            "$omnetRoot\tools\win64\mingw64\bin",
            "$omnetRoot\tools\win64\mingw64\opt\bin"
        )
        
        foreach ($path in $paths) {
            if (Test-Path $path) {
                $env:PATH = "$path;$env:PATH"
                Write-Host "✅ Добавлен в PATH: $path" -ForegroundColor Green
            }
        }
        
        # Установка переменных OMNeT++
        $env:OMNETPP_ROOT = $omnetRoot
        $env:OMNETPP_IMAGE_PATH = "$omnetRoot\images"
        
        Write-Host "✅ Переменные окружения OMNeT++ настроены" -ForegroundColor Green
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

# Создание ini файла для OMNeT++
function New-OMNeTIniFile {
    param(
        [string]$OutputPath,
        [int]$SimTime
    )
    
    $iniContent = @"
[General]
network = IndustrialNetwork
sim-time-limit = ${SimTime}s
cpu-time-limit = 300s
warnings = true
debug-on-errors = true

# Параметры симуляции
seed-set = 1
repeat = 1
sim-time-resolution = us

# Параметры промышленной сети
num_sensors = 3
num_actuators = 2
plc_cycle_time = 1ms
sensor_update_rate = 100ms
actuator_response_time = 10ms

# Сетевые параметры
ethernet_bandwidth = 100Mbps
modbus_timeout = 1000ms
ethercat_cycle_time = 1ms
opc_ua_publish_interval = 100ms

# Параметры протоколов
modbus_enabled = true
ethercat_enabled = true
opc_ua_enabled = true

# Выходные файлы
scalar_file = "$OutputPath\omnetpp.sca"
vector_file = "$OutputPath\omnetpp.vec"
snapshot_file = "$OutputPath\omnetpp.sna"

# Логирование
log_level = INFO
log_format = "%L [%T] %M"
log_file = "$OutputPath\omnetpp.log"

# Визуализация
gui = $($Gui.ToString().ToLower())
qtenv = $($Gui.ToString().ToLower())
cmdenv = $((!$Gui).ToString().ToLower())

# Анализ производительности
record_eventlog = true
eventlog-recording-intervals = "0s..${SimTime}s"
"@
    
    $iniPath = Join-Path $OutputPath "omnetpp.ini"
    $iniContent | Out-File -FilePath $iniPath -Encoding UTF8
    
    Write-Host "✅ Создан ini файл: $iniPath" -ForegroundColor Green
    return $iniPath
}

# Запуск симуляции OMNeT++
function Start-OMNeTSimulation {
    param(
        [string]$ModelPath,
        [string]$OutputPath,
        [string]$IniPath,
        [int]$SimTime
    )
    
    Write-Host "🚀 Запуск симуляции OMNeT++..." -ForegroundColor Green
    Write-Host "Модель: $ModelPath" -ForegroundColor Cyan
    Write-Host "Конфигурация: $IniPath" -ForegroundColor Cyan
    Write-Host "Время симуляции: $SimTime секунд" -ForegroundColor Cyan
    Write-Host "Результаты: $OutputPath" -ForegroundColor Cyan
    
    # Переход в директорию результатов
    Push-Location $OutputPath
    
    try {
        # Определение команды запуска
        if ($Gui) {
            $command = "omnetpp"
            $args = @("-u", "Qtenv", "-c", "General", "-r", "0", $IniPath)
        }
        else {
            $command = "omnetpp"
            $args = @("-u", "Cmdenv", "-c", "General", "-r", "0", $IniPath)
        }
        
        Write-Host "⏳ Выполнение симуляции..." -ForegroundColor Yellow
        Write-Host "Команда: $command $($args -join ' ')" -ForegroundColor Cyan
        
        if ($Verbose) {
            & $command @args
        }
        else {
            & $command @args 2>&1 | Out-Null
        }
        
        Write-Host "✅ Симуляция завершена успешно!" -ForegroundColor Green
        
        # Проверка результатов
        $results = Get-ChildItem -Path "." -Filter "*.sca" | Sort-Object LastWriteTime -Descending
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

# Анализ результатов OMNeT++
function Analyze-OMNeTResults {
    param([string]$OutputPath)
    
    Write-Host "📈 Анализ результатов симуляции OMNeT++..." -ForegroundColor Yellow
    
    $scaFiles = Get-ChildItem -Path $OutputPath -Filter "*.sca"
    $vecFiles = Get-ChildItem -Path $OutputPath -Filter "*.vec"
    
    if ($scaFiles) {
        Write-Host "📊 Скалярные результаты:" -ForegroundColor Green
        foreach ($scaFile in $scaFiles) {
            Write-Host "  - $($scaFile.Name) ($($scaFile.Length) байт)" -ForegroundColor Cyan
            
            # Простой анализ SCA файла
            try {
                $content = Get-Content $scaFile.FullName -Head 20
                $statistics = $content | Where-Object { $_ -match "^\s*\w+" }
                if ($statistics) {
                    Write-Host "    Статистика: $($statistics.Count) записей" -ForegroundColor White
                }
            }
            catch {
                Write-Host "    ⚠️ Не удалось проанализировать SCA файл" -ForegroundColor Yellow
            }
        }
    }
    
    if ($vecFiles) {
        Write-Host "📈 Векторные результаты:" -ForegroundColor Green
        foreach ($vecFile in $vecFiles) {
            Write-Host "  - $($vecFile.Name) ($($vecFile.Length) байт)" -ForegroundColor Cyan
        }
    }
    
    if (-not $scaFiles -and -not $vecFiles) {
        Write-Host "⚠️ Файлы результатов не найдены" -ForegroundColor Yellow
    }
}

# Основная функция
function Main {
    Write-Host "🏭 OMNeT++ Industrial Network Simulator" -ForegroundColor Magenta
    Write-Host "=======================================" -ForegroundColor Magenta
    
    # Проверка установки OMNeT++
    if (-not (Test-OMNeTInstallation)) {
        Write-Host "❌ Не удалось найти OMNeT++. Завершение работы." -ForegroundColor Red
        exit 1
    }
    
    # Проверка зависимостей
    if (-not (Test-OMNeTDependencies)) {
        Write-Host "❌ Не удалось проверить зависимости. Завершение работы." -ForegroundColor Red
        exit 1
    }
    
    # Настройка переменных окружения
    Set-OMNeTEnvironment
    
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
    
    # Создание ini файла
    $iniFile = New-OMNeTIniFile -OutputPath $OutputDir -SimTime $SimulationTime
    
    # Запуск симуляции
    if (Start-OMNeTSimulation -ModelPath $ModelFile -OutputPath $OutputDir -IniPath $iniFile -SimTime $SimulationTime) {
        # Анализ результатов
        Analyze-OMNeTResults $OutputDir
        
        Write-Host "🎉 Симуляция OMNeT++ завершена успешно!" -ForegroundColor Green
        Write-Host "Результаты сохранены в: $OutputDir" -ForegroundColor Cyan
    }
    else {
        Write-Host "❌ Симуляция OMNeT++ завершилась с ошибкой." -ForegroundColor Red
        exit 1
    }
}

# Запуск основной функции
if ($MyInvocation.InvocationName -ne ".") {
    Main
}
