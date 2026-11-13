def lucky_number(num):
    return all(digit in '47' for digit in str(num))


n = int(input())
    
count = sum(1 for digit in str(n) if digit in '47')

if lucky_number(count):
    print("YES")
else:
    print("NO")