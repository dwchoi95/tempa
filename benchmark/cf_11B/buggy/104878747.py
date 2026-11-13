x = (int(input()))
x = abs(x)

jump = 100000
ans = 0
while (jump > 0):
    while (((ans+jump)*(ans+jump+1)/2) <= x) :
        ans += jump
    jump = jump//2

if (((ans + jump)*(ans+jump+1)/2) != x) :
    ans += 2
    
print(ans)