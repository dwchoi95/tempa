palabra = input()
palabra_inicio = palabra[0].upper()
s=""
for i in range(1,len(palabra)):
  s += palabra[i].lower()



print(palabra_inicio + s)