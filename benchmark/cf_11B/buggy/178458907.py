"""
https://codeforces.com/problemset/problem/11/B
"""
position = int(input())


def somme(k):
    return k * (k + 1) // 2


ind = 0
while somme(ind) < position:
    ind += 1

if (somme(ind) - position) % 2 == 0:
    print(ind)
else:
    print(ind + 1)