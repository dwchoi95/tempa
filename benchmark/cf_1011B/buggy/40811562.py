# file_ = open('test.txt')
# f = file_.readline

# input = f

n,m = input().strip().split()
n,m = int(n), int(m)

s = input().strip()
s = [int(i) for i in s.split()]

c = []
for el in set(s):
    c.append(s.count(el))
c.sort()



# pp = 0
# i = 0
# while True:
#     cc = c[i:]
#     p=0
#     for i in range(n):
#         if p>=len(cc):
#            whoops = True
#            break 
#         cc[p] -= 1
#         if cc[p]:
#             continue
#         else:
#             p += 1
#     if not whoops:


altc = c[:]
k = 0
p = 0
whoops = False
prevleast = 0
nn = n
# print(c)
while c:
    if c[0]>=n:
        k = c[0]//n
        while True:
            lmn = 0
            k += 1
            for i in c:
                # print(i,k)
                lmn += i//k
            # print(lmn)
            if lmn<n:
                k = k-1
                print(k)
                exit()
            else:
                continue
            p = max(k, p)
            c.pop(0)
        continue
    least = c.pop(0)
    cc = c[:]
    p = 0
    for i in range(n-1):
        # print(i,n-1,p,cc, least)
        if p>=len(cc):
            # print('whoops')
            whoops = True
            break
        cc[p] -= least
        # print(cc[p]>least)
        if cc[p] >= least:
            continue
        else:
            p += 1
    if not whoops:
        prevleast = least
print(max(prevleast, p))