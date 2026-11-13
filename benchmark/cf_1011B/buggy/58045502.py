pessoa, numeroPacotes = map(int, input().split()) 
pacote = list(input().split())

resultado = list()
if pessoa > numeroPacotes:
    print(0)
    exit(0)
else:
    tipo = pacote[:pessoa]
    for i in tipo:
        resultado.append(pacote.count(i) // tipo.count(i))
print(min(resultado))