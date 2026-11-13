n,m = map(int,input().split())
a = map(int,input().split())
dic = [0] * 101
for x in a:
    dic[x] += 1
def ok(x):
    cnt = 0
    for i in dic:
        cnt += i//x
    return cnt >= n
for x in range(100,0,-1):
    if ok(x):
        print(x)
        exit(0)
print(0)