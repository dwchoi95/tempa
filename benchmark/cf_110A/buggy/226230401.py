def is_almost_lucky_number(n):
    n_str = str(n)
    for digit in n_str:
        """if digit == '7':
            print('YES')"""
        if digit != '4'and digit != '7':
            return "NO"

    return "YES"

n = int(input())
result = is_almost_lucky_number(n)
print(result)