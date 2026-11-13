def process_word(word):
    # Проверяем, соответствует ли слово условиям ошибочно набранного слова
    if word[0].islower():
        # Меняем регистр всех букв на противоположный
        return word.swapcase()
    else:
        # Слово не требует изменения
        return word

# Читаем входные данные
word = input()
# Вызываем функцию для обработки слова
result = process_word(word)
# Выводим результат
print(result)