def is_almost_happy(n):
    n_str = str(n)
    count = 0
    for digit in n_str:
        if digit == '4' or digit == '7':
            count += 1
    if count == 4 or count == 7:
        return "YES"
    else:
        return "NO"
n = int(input())
result = is_almost_happy(n)
print(result)