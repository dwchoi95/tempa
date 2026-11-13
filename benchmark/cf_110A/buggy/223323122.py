def is_nearly_lucky(number):
    lucky_digits = {'4', '7'}
    return all(digit in lucky_digits for digit in str(number))

number = input()

if is_nearly_lucky(number) or number in ['4', '7']:
    print("YES")
else:
    print("NO")