def lucky_number(n):
    n_str = str(n)
    c = 0
    for digit in n_str:
        if digit == "4" or digit == "7":
            c += 1
        else:
            return "NO"
    
    if len(n_str) == c:
        return "YES"

n = int(input())
res = lucky_number(n)
print(res)