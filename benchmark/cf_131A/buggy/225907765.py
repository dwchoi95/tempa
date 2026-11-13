nome = input("Digite um nome: ")

if len(nome) >=1 and len(nome) <= 100:
    teste = nome.lower()

    teste = teste[0].upper() + teste[1::]

    print(teste)