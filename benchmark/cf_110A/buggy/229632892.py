s = input()
ans = 0
x = True
for i in range(len(s)):
    if s[i]=='4' or s[i]=='7':
        ans +=1
    else:
        x = False
if x== False:
    l = str(ans)
    y = True
    for i in range(len(l)):

        if l[i] != '4' and l[i]!='7':
            x = False
        if y:
            print("YES")
        else:
            print("NO")
else:
    print("YES")