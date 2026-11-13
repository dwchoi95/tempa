n = int(input())
n_str = str(n)

lucky = True

digits = len(n_str)
lista = [int(digit) for digit in str(digits)]

for digit in lista:
    if digit != 4 and digit != 7:
        lucky = False

if lucky:
    print("YES")
else:
    print("NO")