word=input()
if word.isupper()==True:
    print(word.lower())
else:
    abc=0
    for a in range(0,len(word),1):
        if word.isupper():
            abc+=1

    if abc ==len(word)-1 and word[1].islower()==True:
        ans=""
        ans+=word[0].isupper()
        ans+=word[1:].islower()