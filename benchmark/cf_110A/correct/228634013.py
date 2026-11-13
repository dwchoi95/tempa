n = int(input())
count = 0

for digit in str(n):
    if digit in '47':
        count += 1

lucky = [4, 7]
is_lucky_count = all(int(digit) in lucky for digit in str(count))

if count > 0 and is_lucky_count:
    print("YES")
else:
    print("NO")