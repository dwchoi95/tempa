n = int(input())
feet = n//36
n %= 36
inch = n//3
if(n%3 == 2):
    inch += 1
if(inch==12):
    feet += 1
    inch =0
print(feet,inch)