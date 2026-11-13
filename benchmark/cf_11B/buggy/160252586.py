step = 1
ans = 0
x = int(input())
if x < 0:
    x = -x
while x > 0:
    x -= step
    step += 1
    ans += 1
if x < 0:
    ans += 1
print(ans)