"""
https://codeforces.com/problemset/problem/125/A

"""
INCHINCM = 3
FOOTININCH=12
FOOTINCM = FOOTININCH * INCHINCM
length = int(input())

feet, rest1 = divmod(length, FOOTINCM)
inches, rest = divmod(rest1, INCHINCM)
inches = inches + 1 if rest > 1 else inches
fff, inches = divmod(inches, FOOTININCH)

print(feet + fff, inches)