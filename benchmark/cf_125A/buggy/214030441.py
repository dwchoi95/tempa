n = int(input())
feet = n//36
n %= 36
inch = n//3
if(n%3 == 2):
    inch += 1
print(feet,inch)