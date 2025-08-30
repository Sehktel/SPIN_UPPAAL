# PowerShell скрипт для автоматизации работы с SPIN
# Автор: Образовательный проект SPIN vs UPPAAL
# Описание: Автоматизирует процесс верификации SPIN моделей

param(
    [string]$ModelPath = "..\models\spin\traffic_light.pml",
    [string]$VerificationPath = "..\models\spin\verification.pml",
    [string]$OutputDir = "..\results",
    [switch]$Basic,
    [switch]$Advanced,
    [switch]$Help
)

# Функция для вывода справки
function Show-Help {
    Write-Host @"
Скрипт для автоматизации работы с SPIN

Использование:
    .\run_spin.ps1 [параметры]

Параметры:
    -ModelPath <путь>        Путь к основной модели (по умолчанию: ../models/spin/traffic_light.pml)
    -VerificationPath <путь> Путь к модели верификации (по умолчанию: ../models/spin/verification.pml)
    -OutputDir <путь>        Директория для результатов (по умолчанию: ../results)
    -Basic                   Запуск только базовой верификации
    -Advanced                Запуск расширенной верификации с тестами
    -Help                    Показать эту справку

Примеры:
    .\run_spin.ps1 -Basic
    .\run_spin.ps1 -Advanced -ModelPath "custom_model.pml"
    .\run_spin.ps1 -Help

"@
}

# Функция для проверки наличия SPIN
function Test-SpinInstallation {
    try {
        $spinVersion = spin -V 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ SPIN найден: $spinVersion" -ForegroundColor Green
            return $true
        }
    }
    catch {
        Write-Host "✗ SPIN не найден в PATH" -ForegroundColor Red
        Write-Host "Пожалуйста, установите SPIN с http://spinroot.com/" -ForegroundColor Yellow
        return $false
    }
    return $false
}

# Функция для проверки наличия компилятора C
function Test-CCompiler {
    try {
        # Проверяем gcc
        $gccVersion = gcc --version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ GCC найден: $($gccVersion[0])" -ForegroundColor Green
            return "gcc"
        }
    }
    catch {
        try {
            # Проверяем clang
            $clangVersion = clang --version 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ Clang найден: $($clangVersion[0])" -ForegroundColor Green
                return "clang"
            }
        }
        catch {
            Write-Host "✗ Компилятор C не найден" -ForegroundColor Red
            Write-Host "Пожалуйста, установите GCC или Clang" -ForegroundColor Yellow
            return $null
        }
    }
    return $null
}

# Функция для создания директории результатов
function Initialize-OutputDirectory {
    if (!(Test-Path $OutputDir)) {
        New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
        Write-Host "✓ Создана директория результатов: $OutputDir" -ForegroundColor Green
    }
}

# Функция для базовой верификации
function Invoke-BasicVerification {
    Write-Host "`n=== ЗАПУСК БАЗОВОЙ ВЕРИФИКАЦИИ ===" -ForegroundColor Cyan
    
    $outputFile = Join-Path $OutputDir "spin_basic_results.txt"
    
    Write-Host "Проверка модели: $ModelPath"
    Write-Host "Результаты будут сохранены в: $outputFile"
    
    # Проверка синтаксиса
    Write-Host "`n1. Проверка синтаксиса модели..." -ForegroundColor Yellow
    spin -a $ModelPath 2>&1 | Tee-Object -FilePath $outputFile
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✓ Синтаксис корректен" -ForegroundColor Green
        
        # Компиляция
        Write-Host "`n2. Компиляция модели..." -ForegroundColor Yellow
        $compiler = Test-CCompiler
        if ($compiler) {
            & $compiler -o pan pan.c -DVECTORSZ=2048 2>&1 | Tee-Object -FilePath $outputFile -Append
            
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ Модель скомпилирована" -ForegroundColor Green
                
                # Запуск верификации
                Write-Host "`n3. Запуск верификации..." -ForegroundColor Yellow
                .\pan.exe -a 2>&1 | Tee-Object -FilePath $outputFile -Append
                
                if ($LASTEXITCODE -eq 0) {
                    Write-Host "✓ Верификация завершена успешно" -ForegroundColor Green
                } else {
                    Write-Host "✗ Верификация завершилась с ошибками" -ForegroundColor Red
                }
            } else {
                Write-Host "✗ Ошибка компиляции" -ForegroundColor Red
            }
        }
    } else {
        Write-Host "✗ Ошибка синтаксиса" -ForegroundColor Red
    }
    
    # Очистка временных файлов
    if (Test-Path "pan.c") { Remove-Item "pan.c" }
    if (Test-Path "pan.exe") { Remove-Item "pan.exe" }
    if (Test-Path "pan") { Remove-Item "pan" }
}

# Функция для расширенной верификации
function Invoke-AdvancedVerification {
    Write-Host "`n=== ЗАПУСК РАСШИРЕННОЙ ВЕРИФИКАЦИИ ===" -ForegroundColor Cyan
    
    $outputFile = Join-Path $OutputDir "spin_advanced_results.txt"
    
    Write-Host "Проверка модели верификации: $VerificationPath"
    Write-Host "Результаты будут сохранены в: $outputFile"
    
    # Проверка синтаксиса
    Write-Host "`n1. Проверка синтаксиса модели верификации..." -ForegroundColor Yellow
    spin -a $VerificationPath 2>&1 | Tee-Object -FilePath $outputFile
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✓ Синтаксис корректен" -ForegroundColor Green
        
        # Компиляция
        Write-Host "`n2. Компиляция модели верификации..." -ForegroundColor Yellow
        $compiler = Test-CCompiler
        if ($compiler) {
            & $compiler -o pan pan.c -DVECTORSZ=2048 -DSAFETY -DNOCLAIM 2>&1 | Tee-Object -FilePath $outputFile -Append
            
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ Модель верификации скомпилирована" -ForegroundColor Green
                
                # Запуск верификации с различными параметрами
                Write-Host "`n3. Запуск верификации безопасности..." -ForegroundColor Yellow
                .\pan.exe -a -m10000 2>&1 | Tee-Object -FilePath $outputFile -Append
                
                Write-Host "`n4. Запуск верификации живости..." -ForegroundColor Yellow
                .\pan.exe -a -l -m10000 2>&1 | Tee-Object -FilePath $outputFile -Append
                
                Write-Host "`n5. Запуск верификации отсутствия deadlock'ов..." -ForegroundColor Yellow
                .\pan.exe -a -m10000 2>&1 | Tee-Object -FilePath $outputFile -Append
                
                Write-Host "✓ Расширенная верификация завершена" -ForegroundColor Green
            } else {
                Write-Host "✗ Ошибка компиляции" -ForegroundColor Red
            }
        }
    } else {
        Write-Host "✗ Ошибка синтаксиса" -ForegroundColor Red
    }
    
    # Очистка временных файлов
    if (Test-Path "pan.c") { Remove-Item "pan.c" }
    if (Test-Path "pan.exe") { Remove-Item "pan.exe" }
    if (Test-Path "pan") { Remove-Item "pan" }
}

# Функция для анализа результатов
function Analyze-Results {
    Write-Host "`n=== АНАЛИЗ РЕЗУЛЬТАТОВ ===" -ForegroundColor Cyan
    
    $basicResults = Join-Path $OutputDir "spin_basic_results.txt"
    $advancedResults = Join-Path $OutputDir "spin_advanced_results.txt"
    
    if (Test-Path $basicResults) {
        Write-Host "`nРезультаты базовой верификации:" -ForegroundColor Yellow
        Get-Content $basicResults | Select-String -Pattern "error|Error|ERROR|deadlock|Deadlock|DEADLOCK" | ForEach-Object {
            Write-Host "  $_" -ForegroundColor Red
        }
    }
    
    if (Test-Path $advancedResults) {
        Write-Host "`nРезультаты расширенной верификации:" -ForegroundColor Yellow
        Get-Content $advancedResults | Select-String -Pattern "error|Error|ERROR|deadlock|Deadlock|DEADLOCK" | ForEach-Object {
            Write-Host "  $_" -ForegroundColor Red
        }
    }
}

# Основная логика скрипта
function Main {
    Write-Host "=== SPIN АВТОМАТИЗАЦИЯ ВЕРИФИКАЦИИ ===" -ForegroundColor Magenta
    Write-Host "Версия: 1.0" -ForegroundColor Gray
    Write-Host "Автор: Образовательный проект SPIN vs UPPAAL" -ForegroundColor Gray
    
    # Проверка параметра справки
    if ($Help) {
        Show-Help
        return
    }
    
    # Проверка зависимостей
    Write-Host "`nПроверка зависимостей..." -ForegroundColor Yellow
    if (!(Test-SpinInstallation)) {
        Write-Host "✗ SPIN не установлен. Завершение работы." -ForegroundColor Red
        return
    }
    
    if (!(Test-CCompiler)) {
        Write-Host "✗ Компилятор C не найден. Завершение работы." -ForegroundColor Red
        return
    }
    
    # Проверка существования файлов
    if (!(Test-Path $ModelPath)) {
        Write-Host "✗ Основная модель не найдена: $ModelPath" -ForegroundColor Red
        return
    }
    
    if ($Advanced -and !(Test-Path $VerificationPath)) {
        Write-Host "✗ Модель верификации не найдена: $VerificationPath" -ForegroundColor Red
        return
    }
    
    # Инициализация директории результатов
    Initialize-OutputDirectory
    
    # Запуск верификации
    if ($Basic -or (!$Basic -and !$Advanced)) {
        Invoke-BasicVerification
    }
    
    if ($Advanced) {
        Invoke-AdvancedVerification
    }
    
    # Анализ результатов
    Analyze-Results
    
    Write-Host "`n=== ВЕРИФИКАЦИЯ ЗАВЕРШЕНА ===" -ForegroundColor Magenta
    Write-Host "Результаты сохранены в: $OutputDir" -ForegroundColor Green
}

# Запуск основной функции
Main
