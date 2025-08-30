#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Базовый конвертер ST в Promela для простых конструкций
    
.DESCRIPTION
    Конвертирует базовые конструкции ST в Promela:
    - IF/THEN/ELSE
    - CASE/OF
    - Простые присваивания
    - Базовые циклы
    
.PARAMETER InputFile
    Путь к ST файлу для конвертации
    
.PARAMETER OutputFile
    Путь для сохранения Promela модели
    
.PARAMETER Help
    Показать справку
#>

param(
    [string]$InputFile,
    [string]$OutputFile,
    [switch]$Help
)

# Функция отображения справки
function Show-Help {
    Write-Host "=== ST В PROMELA КОНВЕРТЕР ===" -ForegroundColor Cyan
    Write-Host ""
    Write-Host "Использование:" -ForegroundColor Yellow
    Write-Host "  .\st2promela_converter.ps1 -InputFile 'input.st' -OutputFile 'output.pml'"
    Write-Host ""
    Write-Host "Параметры:" -ForegroundColor Yellow
    Write-Host "  -InputFile         ST файл для конвертации"
    Write-Host "  -OutputFile        Файл для сохранения Promela модели"
    Write-Host "  -Help              Показать эту справку"
    Write-Host ""
    Write-Host "Поддерживаемые конструкции:" -ForegroundColor Yellow
    Write-Host "  - IF/THEN/ELSE"
    Write-Host "  - CASE/OF"
    Write-Host "  - Простые присваивания"
    Write-Host "  - Базовые циклы FOR"
    Write-Host ""
    Write-Host "Пример:" -ForegroundColor Yellow
    Write-Host "  .\st2promela_converter.ps1 -InputFile 'pump_control.st' -OutputFile 'pump_control.pml'"
}

# Функция конвертации IF/THEN/ELSE
function Convert-IfThenElse {
    param([string]$stCode)
    
    $promelaCode = $stCode
    
    # Замена IF/THEN/ELSE на if/fi
    $promelaCode = $promelaCode -replace 'IF\s+', 'if '
    $promelaCode = $promelaCode -replace '\s+THEN\s*', ' -> '
    $promelaCode = $promelaCode -replace '\s+ELSE\s*', ':: else -> '
    $promelaCode = $promelaCode -replace '\s+END_IF;?\s*', 'fi'
    
    # Замена операторов
    $promelaCode = $promelaCode -replace 'AND', '&&'
    $promelaCode = $promelaCode -replace 'OR', '||'
    $promelaCode = $promelaCode -replace 'NOT', '!'
    $promelaCode = $promelaCode -replace ':=', '='
    
    return $promelaCode
}

# Функция конвертации CASE/OF
function Convert-CaseOf {
    param([string]$stCode)
    
    $promelaCode = $stCode
    
    # Замена CASE/OF на if/fi
    $promelaCode = $promelaCode -replace 'CASE\s+(\w+)\s+OF', 'if'
    $promelaCode = $promelaCode -replace '(\d+):\s*', ':: $1 -> '
    $promelaCode = $promelaCode -replace 'ELSE\s*', ':: else -> '
    $promelaCode = $promelaCode -replace 'END_CASE;?\s*', 'fi'
    
    return $promelaCode
}

# Функция конвертации циклов FOR
function Convert-ForLoop {
    param([string]$stCode)
    
    $promelaCode = $stCode
    
    # Замена FOR/TO/DO на do/od
    if ($stCode -match 'FOR\s+(\w+)\s*:=\s*(\d+)\s+TO\s+(\d+)\s+DO') {
        $var = $matches[1]
        $start = $matches[2]
        $end = $matches[3]
        
        $promelaCode = $stCode -replace 'FOR\s+\w+\s*:=\s*\d+\s+TO\s+\d+\s+DO\s*', "do`n"
        $promelaCode = $promelaCode -replace '\s+END_FOR;?\s*', ":: $var > $end -> break`nod"
        
        # Добавление инициализации и инкремента
        $promelaCode = "$var = $start;`n$promelaCode"
        $promelaCode = $promelaCode -replace '(\w+)\s*:=\s*(\w+);', '$1 = $2;'
    }
    
    return $promelaCode
}

# Функция конвертации переменных
function Convert-Variables {
    param([string]$stCode)
    
    $promelaCode = $stCode
    
    # Замена типов ST на Promela
    $promelaCode = $promelaCode -replace 'BOOL', 'bool'
    $promelaCode = $promelaCode -replace 'INT', 'int'
    $promelaCode = $promelaCode -replace 'REAL', 'float'
    $promelaCode = $promelaCode -replace 'STRING', 'chan'
    
    # Замена объявлений переменных
    $promelaCode = $promelaCode -replace 'VAR\s*', '// ST Variables:'
    $promelaCode = $promelaCode -replace 'END_VAR\s*', '// End Variables'
    
    return $promelaCode
}

# Функция конвертации функций
function Convert-Functions {
    param([string]$stCode)
    
    $promelaCode = $stCode
    
    # Замена FUNCTION на inline
    $promelaCode = $promelaCode -replace 'FUNCTION\s+(\w+)\s*:\s*(\w+)', 'inline $1()'
    $promelaCode = $promelaCode -replace 'END_FUNCTION\s*', '// End Function'
    
    return $promelaCode
}

# Функция создания Promela заголовка
function New-PromelaHeader {
    param([string]$stCode)
    
    $header = @"
/*
 * Автоматически сгенерированная Promela модель из ST кода
 * ВНИМАНИЕ: Требует ручной проверки и доработки!
 */

// Извлеченные переменные из ST кода
"@
    
    # Извлечение переменных из ST кода
    $variables = @()
    if ($stCode -match 'VAR(.*?)END_VAR') {
        $varSection = $matches[1]
        $varLines = $varSection -split "`n" | Where-Object { $_ -match '\w+\s*:\s*\w+' }
        foreach ($line in $varLines) {
            if ($line -match '(\w+)\s*:\s*(\w+)') {
                $varName = $matches[1]
                $varType = $matches[2]
                $promelaType = switch ($varType) {
                    'BOOL' { 'bool' }
                    'INT' { 'int' }
                    'REAL' { 'float' }
                    default { 'int' }
                }
                $variables += "$promelaType $varName;"
            }
        }
    }
    
    if ($variables.Count -eq 0) {
        $variables += "// Переменные не найдены в ST коде"
        $variables += "int example_variable;"
    }
    
    $header += "`n" + ($variables -join "`n")
    $header += @"

// Основной процесс
proctype ST_Process() {
    do
"@
    
    return $header
}

# Функция создания Promela завершения
function New-PromelaFooter {
    $footer = @"
    od
}

// Инициализация
init {
    run ST_Process()
}
"@
    return $footer
}

# Основная функция конвертации
function Convert-STtoPromela {
    param([string]$stCode)
    
    Write-Host "Конвертация ST в Promela..." -ForegroundColor Green
    
    # Создание заголовка
    $promelaCode = New-PromelaHeader -stCode $stCode
    
    # Конвертация основных конструкций
    $convertedCode = $stCode
    
    # Конвертация переменных
    $convertedCode = Convert-Variables -stCode $convertedCode
    
    # Конвертация IF/THEN/ELSE
    $convertedCode = Convert-IfThenElse -stCode $convertedCode
    
    # Конвертация CASE/OF
    $convertedCode = Convert-CaseOf -stCode $convertedCode
    
    # Конвертация циклов FOR
    $convertedCode = Convert-ForLoop -stCode $convertedCode
    
    # Конвертация функций
    $convertedCode = Convert-Functions -stCode $convertedCode
    
    # Извлечение основной логики
    $mainLogic = ""
    $lines = $convertedCode -split "`n"
    foreach ($line in $lines) {
        if ($line -match '^\s*(if|::|do|od|fi)') {
            $mainLogic += "        $line`n"
        } elseif ($line -match '^\s*(\w+\s*[=:]\s*\w+)') {
            $mainLogic += "        $line`n"
        }
    }
    
    if ($mainLogic -eq "") {
        $mainLogic = "        // Основная логика не найдена`n        skip`n"
    }
    
    $promelaCode += $mainLogic
    
    # Создание завершения
    $promelaCode += New-PromelaFooter
    
    return $promelaCode
}

# Основная логика скрипта
if ($Help) {
    Show-Help
    exit 0
}

if (!$InputFile -or !$OutputFile) {
    Write-Host "Ошибка: Необходимо указать входной и выходной файлы" -ForegroundColor Red
    Show-Help
    exit 1
}

if (!(Test-Path $InputFile)) {
    Write-Host "Ошибка: Входной файл не найден: $InputFile" -ForegroundColor Red
    exit 1
}

try {
    # Чтение ST файла
    Write-Host "Чтение ST файла: $InputFile" -ForegroundColor Yellow
    $stCode = Get-Content $InputFile -Raw -Encoding UTF8
    
    # Конвертация
    $promelaCode = Convert-STtoPromela -stCode $stCode
    
    # Сохранение результата
    Write-Host "Сохранение Promela модели: $OutputFile" -ForegroundColor Yellow
    $promelaCode | Out-File -FilePath $OutputFile -Encoding UTF8
    
    Write-Host "✓ Конвертация завершена успешно!" -ForegroundColor Green
    Write-Host "⚠ ВНИМАНИЕ: Требуется ручная проверка и доработка модели" -ForegroundColor Yellow
    
} catch {
    Write-Host "Ошибка конвертации: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}
