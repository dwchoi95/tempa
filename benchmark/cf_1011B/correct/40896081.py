a=input().split()
n=int(a[0])
m=int(a[1])
a=input().split()
dic = {}
for i in a:
    dic[i] = 0
for i in a:
    dic[i] += 1
maxv = int(max(dic.values()))
flag = False
for i in range(maxv,0,-1):
    c=0
    for j in dic:
        c += dic[j]//i
    if c>=n:
        flag=True
        break
if flag:
    print(i)
else:
    print(0)