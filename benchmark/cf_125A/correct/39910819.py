num = int(input())
inches = num//3
if num%3>=2:
    inches+=1
print(inches//12," ", inches%12)