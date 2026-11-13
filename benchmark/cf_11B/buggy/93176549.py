from math import ceil, sqrt, floor, trunc

x = abs(int(input()))

l = (-1 + sqrt(1 + 8*x)) / 2
if l - trunc(l) != 0:
    l = ceil(l)
    
    if l % 2 == 0:
        if (l + 2) % 4 != 0:
            l += 1
    else:
        if (l + 3) % 4 != 0:
            l += 2
l = int(l)
print(l)