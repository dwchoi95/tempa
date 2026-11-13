cm = int(input("Enter length in centimeter : "))
b = cm // 3
a = b // 12
b = b % 12
cm = cm % 3
if cm >= 2:
    b=b+1
print(f"{a} {b}")