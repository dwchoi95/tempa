n=int(input())
s=str(n)
sum=0
for i in s:
    if i=='4' or i=='7':
        sum+=1
s1=str(sum)
for i in s1:
    if i=='4' or i=='7':
        pass
    else:
        print("NO")
        break;
else:
    print("YES")