def srk(n,k,l):
    if k<n:
        return 0
    else:
        se=set(l)
        le=list(se)
        if len(le)==1:
            return k//n
        else:
            return k//len(le) 

n,k=map(int , input().split())
l=[int(x) for x in input().split()]
print(srk(n,k,l))