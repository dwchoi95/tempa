def is_lucky(num):
    return all(digit in '47' for digit in str(num))

n=int(input())
lucky_digit_count=sum(1 for digit in str(n) if digit in '47')

if is_lucky(lucky_digit_count):
    print("YES")
else:
    print("NO")