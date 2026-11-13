n = float(input())
feet = int(n / 36 + 0.5)
r = n - 36 * feet
inch = int(r / 3 + 0.5)
print(feet,'  ',inch)