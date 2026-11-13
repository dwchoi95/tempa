n = int(input())
if n%3==0:
    inc = n//3
elif n%3==1:
    inc = n//3
else:
    inc = n//3 + 1

feet = inc//12
inc = inc%12
print(feet, inc)