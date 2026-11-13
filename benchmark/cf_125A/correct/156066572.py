n = int(input())
inches = round(n / 3)
feet = inches // 12
inches = inches % 12
print(feet, inches)