n,m=map(int,input().split())
book1=[int(x) for x in input().split()]
book2=set(book1)
book3=list(book2)
num=[]
for i in range(len(book3)):
    num.append(book1.count(book3[i]))

if m < n :
    print(0)
elif m==n :
    print(1)

else :
    day=m//n
    while day :
        people=0
        for i in range(len(num)):
            people +=num[i]//day

        if people >= n :
            break
        else :
            day=day-1

    print(day)