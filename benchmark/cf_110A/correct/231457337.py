n = input()
lucky_digits = n.count('4') + n.count('7')

lucky_count = 0
for digit in str(lucky_digits):
    if digit == '4' or digit == '7':
        lucky_count += 1

if lucky_count == len(str(lucky_digits)):
    print("YES")
else:
    print("NO")