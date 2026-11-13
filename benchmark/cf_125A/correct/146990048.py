n = int(input())
inc = n//3
rem = n%3
inc += 1 if rem == 2 else 0
ft = inc//12
inc = inc%12
print(ft, inc)