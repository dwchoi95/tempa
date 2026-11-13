x = abs(int(input()))
csc = []

for i in range(0, 45000):
    csc.append(i * (i + 1) // 2)

def solve(csc, x):
    for i in range(45000 + 1):
        if x == csc[i]:
            return i
        elif x < csc[i]:
            lower_rem = x - csc[i - 1]
            larger_rem = csc[i] - x
            a = float('inf')
            if lower_rem % 2 == 0:
                a = i
            b = i - 1 + lower_rem * 2
            c = i + larger_rem * 2
            return min(a, b, c)

print(solve(csc, x))