lucky = [4,7]

n = input()
if 1<=len(n)<=pow(10,18):
    i = 0
    count = 0
    while i < len(n):
        x = int(n[i])
        if x in lucky:
            count += 1
        i += 1

    if count == i:
        print('YES')
    else:
        print('NO')