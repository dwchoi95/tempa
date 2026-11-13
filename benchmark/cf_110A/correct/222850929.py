def es_afortunado(num):

    for digito in str(num):
        if digito not in '47':
            return False
    return True

def contar_digitos_afortunados(num):

    contador = 0
    for digito in str(num):
        if digito in '47':
            contador += 1
    return contador

n = int(input())  
cantidad_digitos_afortunados = contar_digitos_afortunados(n) 

if es_afortunado(cantidad_digitos_afortunados):  
    print("YES")
else:
    print("NO")