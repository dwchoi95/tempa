n,m = map(int,input().split())
l1 = list(map(int,input().split()))
def fun(n,m,l1):
    if n>m:
        return 0
    l2 = dict((l,l1.count(l)) for l in set(l1))
    if len(set(l2.keys()))==1:
        return l2.get(l1[0])//n
    if len(set(l2.values()))==1:
        return l2.get(l1[0])
    for i in l2.values():
        l3 = [ x // i for x in l2.values()]
        if sum(l3)==n:
            return i
    return 0    
print(fun(n,m,l1))