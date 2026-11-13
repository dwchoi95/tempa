def modificar_palabra(p):
  palabra_inicio = palabra[0].upper()
  respuesta=""
  for i in range(1,len(palabra)):
    respuesta += palabra[i].lower()
  respuesta = palabra_inicio + respuesta
  return respuesta




palabra = input()

tam = len(palabra) - 1
num_mayusculas = 0
for i in range(1,len(palabra)):
  if palabra[i].isupper():
    num_mayusculas += 1

if palabra.isupper():
  palabra_min = palabra.lower()
  print(palabra_min)
elif num_mayusculas == tam:
  modificar = modificar_palabra(palabra)
  print(modificar)
else:
  print(palabra)