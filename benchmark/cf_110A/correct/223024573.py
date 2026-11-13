# Función para contar los dígitos afortunados en un número
def count_lucky_digits(number):
    count = 0
    while number > 0:
        digit = number % 10
        if digit == 4 or digit == 7:
            count += 1
        number //= 10
    return count

# Leer el número n
n = int(input())

# Contar los dígitos afortunados en n
lucky_count = count_lucky_digits(n)

# Verificar si el conteo de dígitos afortunados es un número afortunado
if lucky_count == 4 or lucky_count == 7:
    print("YES")
else:
    print("NO")