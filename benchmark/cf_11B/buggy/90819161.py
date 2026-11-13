n = int(input())

for lr, start_, end_ in zip((2,-2), (1, 2*n-1), (2*n+2, 0)):
    for l in range(start_, end_, lr):
        spaces = " " * (n-l//2)*2
        d = [0] * l
        i = 0
        while l // 2 > 0:
            d[i] = i
            d[-i-1] = i
            l -= 2
            i += 1
        else:
            d[i] = i
        print(spaces, end ='')
        print(*d, end = '')
        print(spaces)