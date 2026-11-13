n=int(input())
if n==0:
    print("0")
else:
    a=0
    for i in range(1,1000):
        a=a+i
        if i==n:
            print(i)
            break
        elif i>n:
            print(i+1)
            break