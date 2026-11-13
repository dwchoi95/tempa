import math

n = input()

# size = len(n)
n = int(n)

count = 0

while n:
    r = n % 10
    n = int(n /10)

    if r == 4 or r == 7:
        count += 1    

if count == 4 or count == 7:
    print("YES")
else:
    print("NO")