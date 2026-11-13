def funca(mean,a,h):
    if mean == 0: 
        print("0")
        return 0
    s = 0
    for f in a:
        s+= int(f/mean)
    if s==h: 
        print(mean)
        return 0
    else: 
        mean-=1
        funca(mean,a,h)
inp = input().split()
h = int(inp[0])
e = int(inp[1])
mean = int(e/h)+1
a = [int(f) for f in input().split()]
b = set(a)
c = {f:0 for f in range(1,max(a)+1)}
for f in b:
    for g in a:
        if f==g:
            c[f]+=1
colvo = []
for f,g in c.items():
    colvo.append(int(g))


funca(mean, colvo,h)