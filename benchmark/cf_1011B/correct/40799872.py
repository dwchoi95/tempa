n,k=map(int,input().split())
ar=list(map(int,input().split()))
a=[0]*101
if(n>k):
    print("0")
else:
    for i in range (k):
        x=ar[i]
        a[x]+=1
    maxp=k//n
    while(maxp>1):
        count=0
        flag=0
        for i in range (101):

            count=count+(a[i]//maxp)

            if(count>=n):
                flag=1
                break

        if(flag==1):
            break
        elif(flag==0):
            maxp=maxp-1

    print(maxp)