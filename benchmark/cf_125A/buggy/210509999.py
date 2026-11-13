centimeters = int(input())

inches = centimeters // 3
feet = inches // 12
rem_centimeters = centimeters - feet*12*3
rem_inches = round(rem_centimeters/3)

print(feet, rem_inches)