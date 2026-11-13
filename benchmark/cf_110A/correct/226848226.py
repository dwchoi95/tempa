def luckynums(n):
    alist=[d for d in n]
    count=0
    for xx in alist:
        if xx=="4" or xx=="7":
            count+=1
    if count==4 or count==7 or count==40 or count==70 or count==47 or count==44 or count==77:
        return "YES"
    return "NO"
s=input()
print(luckynums(s))