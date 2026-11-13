def modificar_palabra(palabra):
  palabra_inicio = palabra[0].upper()
  respuesta=""
  for i in range(1,len(palabra)):
    respuesta += palabra[i].lower()
  respuesta = palabra_inicio + respuesta
  return respuesta


palabra = input()

tam = len(palabra)
num_mayusculas = 0
for i in range(len(palabra)):
  if palabra[i].isupper():
    num_mayusculas += 1

if num_mayusculas == tam or num_mayusculas == tam - 1:
  respuesta = modificar_palabra(palabra)
  print(respuesta)
else:
  print(palabra)