n = int(input())
flag = False
while n > 0:
    if n % 10 != 7 and n % 10 != 4:
        flag = True
    n /= 10
if not flag:
    print("YES")
else:
    print("NO")