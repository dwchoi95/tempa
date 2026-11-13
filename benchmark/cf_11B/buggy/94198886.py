try:
    x=int(input())
    count=0
    s=1
    x=abs(x)
    for i in range(1,x+1):
        k=i*(i+1)
        q=(2*x)/k
        if int(q)==1:
           print(i)
           break
except Exception:
    pass