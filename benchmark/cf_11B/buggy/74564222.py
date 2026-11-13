w=int(input())
p=0
i=1
s=0
if w==0:
    print("0")
else:
    for i in range(0,1000000000000):
       
        if  p>=w:
            print(i)
            break
        else:
            w=w-i
            s=s+1