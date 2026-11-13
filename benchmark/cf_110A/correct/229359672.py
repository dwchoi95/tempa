n = input()

def es_numero_de_la_suerte(numero):
    for digito in numero:
        if digito != '4' and digito != '7':
            return False
    return True

def es_numero_de_la_suerte_casi(n):
    conteo_de_suertes = 0
    for digito in n:
        if digito == '4' or digito == '7':
            conteo_de_suertes += 1

    return es_numero_de_la_suerte(str(conteo_de_suertes))

if es_numero_de_la_suerte_casi(n):
    print('YES')
else:
    print('NO')