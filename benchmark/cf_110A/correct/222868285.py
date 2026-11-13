n = int(input())
count = 0
while n > 0:
    m = n % 10  
    if m == 4 or m == 7:
        count += 1
    n //= 10 
if count == 4 or count == 7:
    print("YES")
else:
    print("NO")