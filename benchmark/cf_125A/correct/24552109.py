n = int(input())

if n % 36 == 35:
    print((n + 1) // 36, 0)
else:
    feet = n // 36
    cm = n - feet * 36

    inches = cm // 3
    if cm % 3 == 2:
        inches += 1

    print(feet, inches)