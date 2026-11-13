n = int(input())
inch = n//3
if n%3 == 2: inch += 1
feet = inch//12
inch = inch%12
print(feet,inch)