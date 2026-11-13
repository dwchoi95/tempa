n = int(input())

lucky_count = 0

for digit in str(n):
    if digit == '4' or digit == '7':
        lucky_count += 1

lucky_count_str = str(lucky_count)

if all(digit == '4' or digit == '7' for digit in lucky_count_str):
    if lucky_count_str.count('4') == 0 or lucky_count_str.count('7') == 0:
        print("YES")
    else:
        print("NO")
else:
    print("NO")