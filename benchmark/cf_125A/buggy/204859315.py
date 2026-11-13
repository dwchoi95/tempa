"""
https://codeforces.com/problemset/problem/125/A

"""
INCHINCM = 3
FOOTINCM = 12 * 3

length = int(input())

feet, rest = divmod(length, FOOTINCM)

inches, rest = divmod(rest, INCHINCM)

print(feet, inches + 1 if rest > 1 else inches)