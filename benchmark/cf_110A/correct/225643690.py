numero = input("")
if int(numero)<0 or int(numero)>10**18:
    exit(1)
conta = 0
for i in range(len(numero)):
    if numero[i]=='4' or numero[i]=='7':
        conta += 1
if conta==4 or conta==7:
    print('YES')
else:
    print('NO')