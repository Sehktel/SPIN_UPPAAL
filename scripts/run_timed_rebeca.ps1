# PowerShell скрипт для запуска Timed Rebeca
# Запуск актор-ориентированных моделей с временными ограничениями
# Автор: Senior Developer
# Дата: 2024-12-19

param(
    [string]$ModelPath = "models/timed_rebeca/distributed_control_system.rebeca",
    [string]$OutputPath = "results/timed_rebeca_output.txt",
    [int]$Timeout = 30000,  # 30 секунд
    [switch]$Verbose
)

# Цвета для вывода
$Colors = @{
    Info = "Cyan"
    Success = "Green"
    Warning = "Yellow"
    Error = "Red"
    Header = "Magenta"
}

# Функция для цветного вывода
function Write-ColorOutput {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    
    if ($Verbose) {
        Write-Host $Message -ForegroundColor $Colors[$Color]
    } else {
        Write-Host $Message
    }
}

# Функция для вывода заголовка
function Write-Header {
    param([string]$Title)
    
    Write-ColorOutput "`n" -Color Header
    Write-ColorOutput "=" * $Title.Length -Color Header
    Write-ColorOutput $Title -Color Header
    Write-ColorOutput "=" * $Title.Length -Color Header
    Write-ColorOutput "" -Color Header
}

# Функция для проверки зависимостей
function Test-Dependencies {
    Write-Header "Проверка зависимостей"
    
    # Проверка Java
    try {
        $javaVersion = java -version 2>&1 | Select-String "version"
        if ($javaVersion) {
            Write-ColorOutput "✅ Java найден: $javaVersion" -Color Success
        } else {
            Write-ColorOutput "❌ Java не найден" -Color Error
            return $false
        }
    } catch {
        Write-ColorOutput "❌ Java не найден" -Color Error
        return $false
    }
    
    # Проверка Timed Rebeca
    $rebecaPath = Get-Command "rebeca" -ErrorAction SilentlyContinue
    if ($rebecaPath) {
        Write-ColorOutput "✅ Timed Rebeca найден: $($rebecaPath.Source)" -Color Success
    } else {
        Write-ColorOutput "⚠️ Timed Rebeca не найден в PATH" -Color Warning
        Write-ColorOutput "   Установите Timed Rebeca или добавьте в PATH" -Color Warning
    }
    
    return $true
}

# Функция для компиляции модели
function Compile-Model {
    param([string]$ModelPath)
    
    Write-Header "Компиляция модели"
    
    if (-not (Test-Path $ModelPath)) {
        Write-ColorOutput "❌ Модель не найдена: $ModelPath" -Color Error
        return $false
    }
    
    Write-ColorOutput "📁 Модель: $ModelPath" -Color Info
    
    try {
        # Создание директории для результатов
        $outputDir = Split-Path $OutputPath -Parent
        if (-not (Test-Path $outputDir)) {
            New-Item -ItemType Directory -Path $outputDir -Force | Out-Null
        }
        
        # Компиляция с помощью Java (если Timed Rebeca не найден)
        if (-not (Get-Command "rebeca" -ErrorAction SilentlyContinue)) {
            Write-ColorOutput "🔧 Компиляция с помощью Java..." -Color Info
            
            # Создание временного Java файла
            $javaFile = $ModelPath -replace '\.rebeca$', '.java'
            Copy-Item $ModelPath $javaFile
            
            # Компиляция Java
            javac $javaFile
            if ($LASTEXITCODE -eq 0) {
                Write-ColorOutput "✅ Компиляция успешна" -Color Success
                return $true
            } else {
                Write-ColorOutput "❌ Ошибка компиляции" -Color Error
                return $false
            }
        } else {
            # Компиляция с помощью Timed Rebeca
            Write-ColorOutput "🔧 Компиляция с помощью Timed Rebeca..." -Color Info
            
            $compileResult = rebeca -c $ModelPath 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-ColorOutput "✅ Компиляция успешна" -Color Success
                return $true
            } else {
                Write-ColorOutput "❌ Ошибка компиляции: $compileResult" -Color Error
                return $false
            }
        }
    } catch {
        Write-ColorOutput "❌ Ошибка компиляции: $($_.Exception.Message)" -Color Error
        return $false
    }
}

# Функция для запуска модели
function Run-Model {
    param([string]$ModelPath)
    
    Write-Header "Запуск модели"
    
    try {
        if (Get-Command "rebeca" -ErrorAction SilentlyContinue) {
            # Запуск с помощью Timed Rebeca
            Write-ColorOutput "🚀 Запуск с помощью Timed Rebeca..." -Color Info
            
            $runResult = rebeca -r $ModelPath 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-ColorOutput "✅ Модель выполнена успешно" -Color Success
                $runResult | Out-File -FilePath $OutputPath -Encoding UTF8
                Write-ColorOutput "📄 Результаты сохранены в: $OutputPath" -Color Success
                return $true
            } else {
                Write-ColorOutput "❌ Ошибка выполнения: $runResult" -Color Error
                return $false
            }
        } else {
            # Запуск с помощью Java
            Write-ColorOutput "🚀 Запуск с помощью Java..." -Color Info
            
            $javaFile = $ModelPath -replace '\.rebeca$', '.java'
            $className = (Get-Item $javaFile).BaseName
            
            # Запуск с таймаутом
            $job = Start-Job -ScriptBlock {
                param($ClassName)
                java $ClassName
            } -ArgumentList $className
            
            if (Wait-Job $job -Timeout ($Timeout / 1000)) {
                $result = Receive-Job $job
                Remove-Job $job
                
                if ($LASTEXITCODE -eq 0) {
                    Write-ColorOutput "✅ Модель выполнена успешно" -Color Success
                    $result | Out-File -FilePath $OutputPath -Encoding UTF8
                    Write-ColorOutput "📄 Результаты сохранены в: $OutputPath" -Color Success
                    return $true
                } else {
                    Write-ColorOutput "❌ Ошибка выполнения" -Color Error
                    return $false
                }
            } else {
                Stop-Job $job
                Remove-Job $job
                Write-ColorOutput "❌ Таймаут выполнения ($($Timeout)ms)" -Color Error
                return $false
            }
        }
    } catch {
        Write-ColorOutput "❌ Ошибка выполнения: $($_.Exception.Message)" -Color Error
        return $false
    }
}

# Функция для анализа результатов
function Analyze-Results {
    param([string]$OutputPath)
    
    Write-Header "Анализ результатов"
    
    if (-not (Test-Path $OutputPath)) {
        Write-ColorOutput "❌ Файл результатов не найден" -Color Error
        return
    }
    
    try {
        $content = Get-Content $OutputPath -Encoding UTF8
        
        # Анализ логов
        $logLines = $content | Where-Object { $_ -match '\[.*\]' }
        $errorLines = $content | Where-Object { $_ -match 'ERROR|ОШИБКА|FAILED|КРИТИЧНО' }
        $warningLines = $content | Where-Object { $_ -match 'WARNING|ВНИМАНИЕ|WARN' }
        
        Write-ColorOutput "📊 Статистика выполнения:" -Color Info
        Write-ColorOutput "   Всего строк: $($content.Count)" -Color Info
        Write-ColorOutput "   Логов: $($logLines.Count)" -Color Info
        Write-ColorOutput "   Ошибок: $($errorLines.Count)" -Color Info
        Write-ColorOutput "   Предупреждений: $($warningLines.Count)" -Color Info
        
        if ($errorLines.Count -gt 0) {
            Write-ColorOutput "`n❌ Ошибки:" -Color Error
            $errorLines | ForEach-Object { Write-ColorOutput "   $_" -Color Error }
        }
        
        if ($warningLines.Count -gt 0) {
            Write-ColorOutput "`n⚠️ Предупреждения:" -Color Warning
            $warningLines | ForEach-Object { Write-ColorOutput "   $_" -Color Warning }
        }
        
        # Поиск временных метрик
        $timeMetrics = $content | Where-Object { $_ -match '\d+ms|\d+ms\)' }
        if ($timeMetrics.Count -gt 0) {
            Write-ColorOutput "`n⏱️ Временные метрики:" -Color Info
            $timeMetrics | ForEach-Object { Write-ColorOutput "   $_" -Color Info }
        }
        
    } catch {
        Write-ColorOutput "❌ Ошибка анализа результатов: $($_.Exception.Message)" -Color Error
    }
}

# Функция для очистки временных файлов
function Cleanup-TempFiles {
    Write-Header "Очистка временных файлов"
    
    try {
        $tempFiles = @(
            ($ModelPath -replace '\.rebeca$', '.java'),
            ($ModelPath -replace '\.rebeca$', '.class')
        )
        
        foreach ($file in $tempFiles) {
            if (Test-Path $file) {
                Remove-Item $file -Force
                Write-ColorOutput "🗑️ Удален: $file" -Color Info
            }
        }
        
        Write-ColorOutput "✅ Очистка завершена" -Color Success
    } catch {
        Write-ColorOutput "⚠️ Ошибка очистки: $($_.Exception.Message)" -Color Warning
    }
}

# Главная функция
function Main {
    Write-Header "Timed Rebeca - Запуск модели"
    Write-ColorOutput "🎯 Цель: Запуск актор-ориентированной модели с временными ограничениями" -Color Info
    Write-ColorOutput "📁 Модель: $ModelPath" -Color Info
    Write-ColorOutput "⏱️ Таймаут: $($Timeout)ms" -Color Info
    
    # Проверка зависимостей
    if (-not (Test-Dependencies)) {
        Write-ColorOutput "❌ Критические зависимости не найдены" -Color Error
        exit 1
    }
    
    # Компиляция модели
    if (-not (Compile-Model $ModelPath)) {
        Write-ColorOutput "❌ Ошибка компиляции модели" -Color Error
        exit 1
    }
    
    # Запуск модели
    if (-not (Run-Model $ModelPath)) {
        Write-ColorOutput "❌ Ошибка выполнения модели" -Color Error
        exit 1
    }
    
    # Анализ результатов
    Analyze-Results $OutputPath
    
    # Очистка
    Cleanup-TempFiles
    
    Write-Header "Завершено"
    Write-ColorOutput "🎉 Модель Timed Rebeca успешно выполнена!" -Color Success
    Write-ColorOutput "📄 Результаты сохранены в: $OutputPath" -Color Success
}

# Запуск главной функции
try {
    Main
} catch {
    Write-ColorOutput "❌ Критическая ошибка: $($_.Exception.Message)" -Color Error
    exit 1
}
