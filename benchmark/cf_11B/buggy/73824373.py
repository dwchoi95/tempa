from math import floor,ceil,sqrt
x=int(input())
n=(-1+sqrt(1+(8*x)))//2
upper=(n+1)*(n+2)/2
lower=n*(n+1)/2
print(n,upper,lower)
if (x-lower)<=(upper-x):
    print(int(n+(x-lower)*2))
else:
    print(int(n+1+(upper-x)*2))