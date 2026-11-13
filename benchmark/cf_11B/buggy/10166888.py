a=int(input())

s=0
i=1
p=0
if a==0:
    print(0)
else:

    for i in range(1,a**2):
        p=((i+1)*i)//2
        if p==a:
            print(i)
            break
        if p>a:
            p=((i-1)*i)//2
            i=i-1
            s=1
            break
    if s==1:

        m=i+(a-p)*2

        print(m)