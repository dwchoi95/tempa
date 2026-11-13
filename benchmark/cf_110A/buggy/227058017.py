n = int(input())
def is_lucky(number):
    while number > 0:
        digit = number % 10
        if digit != 4 and digit != 7:
            return False
        number //= 10
    return True
lucky_count = 0
while n > 0:
    digit = n % 10
    if digit == 4 or digit == 7:
        lucky_count += 1
    n //= 10

if is_lucky(lucky_count):
    print("YES")
else:
    print("NO")