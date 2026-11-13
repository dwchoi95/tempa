n, m = list(input().split())
n, m = [int(n), int(m)]
ls = list(map(int, list(input().split())))
dic = {i:0 for i in range(1, 101)}
for i in ls:
    dic[i] += 1
days = 0
for i in range(1, 1000):
    temp_m = n
    for j in dic.values():
        if temp_m <= 0:
            break
        if j >= i:
            temp_m = temp_m - j//i
    if temp_m <= 0:
        days = i
    else:
        break
print(days)