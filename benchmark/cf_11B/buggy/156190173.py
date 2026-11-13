x = abs(int(input()))
csc = []

for i in range(0, 45000):
    csc.append(i * (i + 1) // 2)

def solve(csc, x):
    for i in range(45000 + 1):
        if x == csc[i]:
            return i + 1
        elif x < csc[i]:
            lower_rem = x - csc[i - 1]
            larger_rem = csc[i] - x
            return i + 1 if lower_rem % 2 == 0 else i + 1 + larger_rem * 2

print(solve(csc, x))