def is_lucky(num):
    return set(str(num)) <= {'4', '7'}


n = int(input())


lucky_digits_count = str(n).count('4') + str(n).count('7')


if is_lucky(lucky_digits_count):
    print("YES")
else:
    print("NO")