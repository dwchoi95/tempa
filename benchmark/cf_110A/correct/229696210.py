def nearly_lucky(n):

    lucky = ['4', '7']
    c = 0

    for digit in str(n):
        if digit in lucky:
            c += 1
    
    return c == 4 or c == 7

n = input()

result = nearly_lucky(n)

print('YES' if result else 'NO')