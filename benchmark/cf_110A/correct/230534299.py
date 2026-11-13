def is_lucky_digit(digit):
    return digit=='4' or digit=='7'
def is_nearly_lucky(n):
    count_lucky_digits=0
    for digit in str(n):
        if is_lucky_digit(digit):
            count_lucky_digits+=1
    return is_lucky_digit(str(count_lucky_digits))

n=int(input())
if is_nearly_lucky(n):
    print("YES")
else:
    print("NO")