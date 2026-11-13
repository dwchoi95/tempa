def lucky_number(n):
    for i in n:
        if i != '4' and i != '7':
            return "No"
    return "Yes"

n = input()
res = lucky_number(n)
print(res)