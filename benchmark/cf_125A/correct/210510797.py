centimeters = int(input())

feet = centimeters // 36
rem_centimeters1 = (centimeters - feet*12*3)
inches = rem_centimeters1 // 3
rem_centimeters2 = rem_centimeters1 - (inches*3)

if rem_centimeters2 >= 1.5:
    inches += 1
    if inches == 12:
        feet += 1
        inches = 0

print(feet, inches)