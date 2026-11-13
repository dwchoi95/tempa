def lucky1(l):
    for i in l:
        if i!=4 and i!=7:
            return False
        else:
            return True
def lucky2(l):
    for i in l:
        if i!=4 and i!=7:
            return False
        else:
            return True
def Turnlist(n):
    n=list(n)
    for i in range(len(n)):
        n[i]=int(n[i])
    return n




n=input()
m=len(n)
m=str(m)
n=Turnlist(n)
m=Turnlist(m)


if lucky1(n) and lucky2(m):
    print("YES")
else:
    print("NO")