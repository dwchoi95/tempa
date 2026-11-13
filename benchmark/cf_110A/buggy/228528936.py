def digit(x):
    digits = []
    while(x != 0):
        digits.append(x % 10)
        x = x // 10

    return digits

def lucky(x):
    l = digit(x)
    if len(l) == 0:
        return 'NO'
    for i in range(len(l)):
        if l[i] != '4' and l[i] != '7':
            return 'NO'
        else:
            return 'YES'

n = int(input())
d = digit(n)
flag = 0
for i in range(len(d)):
    if lucky(d[i]) == 'YES':
        flag += 1
print(lucky(flag))