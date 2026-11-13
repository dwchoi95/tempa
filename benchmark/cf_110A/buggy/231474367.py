n=input()
c=0
for d in n:
    if d=='4' or d=='7':
        c+=1
    if set(str(c))<=set('47'):
        print("YES")
    else:
        print("NO")