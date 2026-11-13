n = int(input())
count = 0
while n != 0:
    if (n % 10 in [4, 7]):
        count += 1
    n //= 10

while count != 0:
    if count % 10 not in [4, 7]:
        print("NO")
        exit(0)
    count //= 10

print("YES")