def count_lucky_digits(n):
    count = 0
    while n > 0:
        if n % 10 == 4 or n % 10 == 7:
            count += 1
        n //= 10
    return count
 
n = int(input())
lucky_count = count_lucky_digits(n)
 
if lucky_count == 4 or lucky_count == 7:
    print("YES")
else:
    print("NO")