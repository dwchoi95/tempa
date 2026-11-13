__author__ = 'Darren'


def solve():
    from math import ceil
    x = abs(int(input()))
    k = ceil(((8 * x + 1) ** 0.5 - 1) / 2)
    location = k * (k + 1) // 2
    if location == x:
        print(k)
    elif ((location - x) + (k + 1)) % 2 == 0:
        print(k+1)
    else:
        print(k+2)


if __name__ == '__main__':
    solve()