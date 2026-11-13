s=input()
c=0
for ele in s:
    if ele=='4' or ele=='7':
        c=c+1
if c==7 or c==4:
    print("YES")
else:
    print("NO")