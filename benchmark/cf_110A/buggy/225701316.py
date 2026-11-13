x = int(input())
while x > 0:
    rem = x%10
    x = x//10
    if rem == 4 or rem == 7:
        count = True
    else:
        count = False
        break
if count:
    print("YES")
else:
    print("NO")