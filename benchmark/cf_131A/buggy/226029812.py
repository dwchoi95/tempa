nome = input()
res = ''
isTudolower = True

if(nome.isalpha() and len(nome) > 0):
    for i in nome:
        if(i.isupper()):
            isTudolower = False

    if len(nome) > 0 and len(nome) <= 100 and isTudolower == False:
        teste = nome.lower()
        a = teste[0].upper()
        b = teste[1::].lower()
        res = a + b
        print(res.capitalize())
    else:
        res = nome
        print(res)