# from math import ceil

t = 1
for test in range(t):
    n, m = map(int, input().split())
    a = list(map(int, input().split()))
    count = [0 for i in range(101)]
    for i in a:
        count[i]+=1
    count.sort()
    ans = 0
    tmp = 0
    for i in range(1, 101):
        tmp = n
        for j in count:
            tmp-=(j//i)
        if tmp>0:
            break
        else:
            ans = i
    print(ans)