n = input()

lucky_count = n.count('4') + n.count('7')

def is_lucky(number):
    return all(digit in '47' for digit in str(number))

if is_lucky(lucky_count):
    print("YES")
else:
    print("NO")