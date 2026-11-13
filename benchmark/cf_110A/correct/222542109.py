n=list(input())
count=0
for i in range(len(n)):
    # print(n[i])
    if(n[i]=='4' or n[i]=='7'):
        count+=1
m=count
if(m==4 or m==7):
    print("YES")
else:
    print("NO")