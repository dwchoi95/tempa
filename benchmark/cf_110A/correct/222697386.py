n=int(input())
string=str(n)
count=0
for i in range(len(string)):
    if string[i]=='4' or string[i]=='7':
        count+=1
if count==4 or count==7:
    print("YES")
else:
    print("NO")