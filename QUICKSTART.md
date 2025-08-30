# Быстрый старт: SPIN vs UPPAAL

## 🚀 Быстрый запуск за 5 минут

Этот документ поможет вам быстро начать работу с проектом верификации SPIN vs UPPAAL.

## 📋 Предварительные требования

### Для SPIN:
- [SPIN](http://spinroot.com/spin/Man/README.html) - скачайте и установите
- Компилятор C (GCC, Clang, или MSVC)

### Для UPPAAL:
- [UPPAAL](https://uppaal.org/download/) - скачайте и установите
- Java Runtime Environment (JRE)

## ⚡ Быстрый старт

### 1. Клонирование проекта
```powershell
git clone <repository-url>
cd SPIN_UPPAAL
```

### 2. Проверка структуры
```powershell
# Проверяем, что все файлы на месте
tree /f
```

### 3. Запуск SPIN верификации
```powershell
# Переходим в директорию скриптов
cd scripts

# Запускаем базовую верификацию
.\run_spin.ps1 -Basic

# Запускаем расширенную верификацию
.\run_spin.ps1 -Advanced
```

### 4. Запуск UPPAAL верификации
```powershell
# Запускаем симуляцию
.\run_uppaal.ps1 -Simulation

# Запускаем верификацию
.\run_uppaal.ps1 -Verification
```

## 🔍 Что происходит

### SPIN процесс:
1. **Проверка синтаксиса** - анализ Promela модели
2. **Компиляция** - генерация C кода
3. **Верификация** - проверка свойств
4. **Результаты** - сохранение в `results/`

### UPPAAL процесс:
1. **Проверка XML** - валидация модели
2. **Создание скриптов** - для GUI
3. **Отчет** - инструкции по использованию

## 📁 Структура результатов

```
results/
├── spin_basic_results.txt      # Результаты базовой SPIN верификации
├── spin_advanced_results.txt   # Результаты расширенной SPIN верификации
├── uppaal_simulation_results.txt    # Результаты UPPAAL симуляции
├── uppaal_verification_results.txt  # Результаты UPPAAL верификации
├── simulation_script.txt       # Скрипт для UPPAAL симуляции
├── verification_script.txt     # Скрипт для UPPAAL верификации
└── uppaal_report.md           # Отчет по UPPAAL
```

## 🎯 Первые шаги

### Для начинающих:

1. **Изучите модели** в `models/spin/` и `models/uppaal/`
2. **Запустите базовую верификацию** SPIN
3. **Откройте UPPAAL** и загрузите модель
4. **Изучите документацию** в `docs/`
5. **Понять LTL-формулы** - прочитайте `docs/ltl_analysis.md`

### Для продвинутых:

1. **Модифицируйте модели** под свои нужды
2. **Добавьте новые свойства** для верификации
3. **Оптимизируйте производительность**
4. **Интегрируйте в CI/CD**

## 🚨 Решение проблем

### SPIN не найден:
```powershell
# Проверьте установку
spin -V

# Добавьте в PATH или укажите полный путь
$env:PATH += ";C:\path\to\spin"
```

### UPPAAL не найден:
```powershell
# Укажите путь к UPPAAL
.\run_uppaal.ps1 -UppaalPath "C:\path\to\uppaal.jar"
```

### Ошибки компиляции:
```powershell
# Установите компилятор C
# Для Windows: Visual Studio Build Tools
# Для Linux: gcc
# Для macOS: clang
```

## 📚 Следующие шаги

1. **Изучите руководства** в `docs/`
2. **Попробуйте свои модели**
3. **Изучите примеры** в документации
4. **Присоединитесь к сообществу**

## 🆘 Получение помощи

- **Документация**: `docs/` директория
- **Примеры**: `models/` директория
- **Скрипты**: `scripts/` директория
- **Результаты**: `results/` директория

## 🔧 Настройка окружения

### Windows:
```powershell
# Установка Chocolatey (если не установлен)
Set-ExecutionPolicy Bypass -Scope Process -Force; [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; iex ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))

# Установка GCC
choco install mingw

# Установка Java
choco install openjdk
```

### Linux:
```bash
# Ubuntu/Debian
sudo apt update
sudo apt install gcc build-essential openjdk-11-jdk

# CentOS/RHEL
sudo yum install gcc java-11-openjdk-devel
```

### macOS:
```bash
# Установка Homebrew (если не установлен)
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

# Установка инструментов
brew install gcc openjdk
```

## 🎉 Готово!

Теперь у вас есть полностью функциональный проект для изучения SPIN и UPPAAL. Начните с простых примеров и постепенно усложняйте задачи.

**Удачи в изучении формальных методов верификации!** 🚀
