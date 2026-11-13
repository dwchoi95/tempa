n = input()
su = 0
for i in n:
    if i == '4' or i == '7':
        su += 1
if su == 4 or su == 7:
    print("YES")
else:
    print("NO")