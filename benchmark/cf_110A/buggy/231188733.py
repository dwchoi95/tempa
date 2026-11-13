n=input()
a=['1','2','3','5','6','8','9','0']
c=0
if '7'in n and '4' in n:
    c=1
    c1,c2=0,0
    for i in range(len(n)):
        j=len(n)-i-1
        if n[i] in a or n[j]in a:
            c=0
            break    
if c==1:
    print("YES")
else:
    print("NO")