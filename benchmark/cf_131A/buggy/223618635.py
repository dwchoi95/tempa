slovo=input()
stav=True


if len(slovo) != 1 :
    for k in range(1,len(slovo)):
        if slovo[k].islower() == True:
            stav=False

    if stav== True:
        if slovo[0].islower() == True:
            slovo=slovo[0].upper() + slovo[1:].lower()
        elif slovo[0].islower() == False:
            slovo = slovo.lower()

elif len(slovo) == 1 and slovo[0].islower() == True:
    slovo = slovo.upper()


print(slovo)