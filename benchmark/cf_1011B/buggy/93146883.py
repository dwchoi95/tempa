from collections import defaultdict
d = defaultdict(int)
n,m = map(int,input().split())
food_type = list(map(int,input().split()))
for f in food_type:
    d[f] += 1

d_ls = sorted(d.items(), key=lambda k: k[1], reverse=True)
max_d = min(d_ls[0][1], m//n)
print(max_d)
for i in range(1, max_d+1):
    s = sum([f[1] // i for f in d_ls])
    if s < n:
        print(i-1)
        break
print(i)