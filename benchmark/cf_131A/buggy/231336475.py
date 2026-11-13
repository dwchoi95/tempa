word = input()  # Считываем входное слово

# Проверяем, является ли слово набранным с ошибочно нажатой клавишей Caps Lock
if word.isupper() or (len(word) > 1 and word[1:].isupper()):
    word = word.swapcase()  # Меняем регистр всех букв на противоположный

print(word)  # Выводим результат обработки слова