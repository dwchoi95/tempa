n=input()
lis=list(set(list(n)))
lis2=['4','7']
#print(lis,lis2)
def func(lis,lis2):
    flag=True
    for i in lis:
        #print("a")
        if i not in lis2:
            flag=False
            break
    #print(flag)
    return flag


def flagg(f):
    if f==True:
        print("YES")
    else:
        print("NO")
f=False
if len(n)==7 or len(n)==4:
    f=func(lis,lis2)
    func(lis,lis2)
    flagg(f)
else:
    flagg(f)