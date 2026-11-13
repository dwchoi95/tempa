n = int(input())

def es_numero_de_la_suerte(numero):
    while numero > 0:
        digito = numero % 10
        if digito != 4 and digito != 7:
            return False
        numero //= 10
    return True

def es_numero_de_la_suerte_casi(n):
    conteo_de_suertes = 0
    while n > 0:
        digito = n % 10
        if digito == 4 or digito == 7:
            conteo_de_suertes += 1
        n //= 10

    return es_numero_de_la_suerte(conteo_de_suertes)

if es_numero_de_la_suerte_casi(n):
    print('YES')
else:
    print('NO')