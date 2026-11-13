nome = input("")

if len(nome) > 0 and len(nome) <= 100:
    teste = nome.lower()
    print(teste[0].upper() + teste[1::])