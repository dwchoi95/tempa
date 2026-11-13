n = int(input())

if n % 3 == 0:
    b = n // 3
elif n % 3 == 2:
    b = n // 3 + n % 3
else:
    b = n // 3
    
a = b // 12
b %= 12

print(a, b)