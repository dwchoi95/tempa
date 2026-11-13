cm = int(input())
inches = cm // 3
if cm % 3 == 2:
    inches += 1
feet = inches // 12
inches %= 12
print(feet, inches)