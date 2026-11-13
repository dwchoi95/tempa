n = int(input())
digits = [int(digit) for digit in str(n)]

ans = 0
for d in digits:
    if d == 4 or d == 7:
        ans += 1
    
print('YES' if ans == 4 or ans == 7 else 'NO')