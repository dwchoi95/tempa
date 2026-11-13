n = float(input())
inch = int(n / 3 + 0.5)
feet = int(inch / 12)
r = inch - 12 * feet
print(feet,"  ",r)