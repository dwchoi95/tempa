a=int(input())
q=True
while a>0:
    e=a%10
    if not(e==4 or e==7):
        print("NO")
        q=False
        break
    a=a//10
if q:
    print("YES")