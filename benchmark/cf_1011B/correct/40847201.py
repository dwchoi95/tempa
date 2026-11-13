n, m = map(int, input().split())
u = list(map(int, input().split()))
u.sort()
cp = []
cnt = 1
for i in range(1, m):
    if u[i] == u[i - 1]:
        cnt += 1
    else:
        cp.append(cnt)
        cnt = 1
cp.append(cnt)
cp.sort(reverse = 1)
p = len(cp)
def chek(k):
    ind = 0
    cp1 = cp[:]
    for i in range(n):
        while ind < p and cp1[ind] < k:
            ind += 1
        if ind >= p:
            return False
        cp1[ind] -= k
    return True
L = 0
R = cp[0]
while R - L > 1:
    m = (L + R) // 2
    if chek(m):
        L = m
    else:
        R = m
if chek(R):
    print(R)
else:
    print(L)