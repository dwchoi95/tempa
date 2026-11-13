def es_casi_afortunado(n):
    dígitos_suerte = [4, 7]
    count = 0

    while n > 0:
        último_dígito = n % 10
        if último_dígito in dígitos_suerte:
            count += 1
        n //= 10

    return "YES" if count in dígitos_suerte else "NO"

n = int(input())
print(es_casi_afortunado(n))