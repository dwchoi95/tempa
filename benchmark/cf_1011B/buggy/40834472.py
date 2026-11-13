'''
a,b = [int(i) for i in input().split()]
mystr = input()
strarr = [ord(i)-96 for i in sorted(mystr)]

minv = 50*26
for i in range(a):
    count = 1
    current = i
    c= [strarr[i]]
    for o in range(i+1,a):
        if strarr[o] - strarr[current] >= 2:
            count+=1
            current = o
            c.append(strarr[current])
    if count >= b:
        if sum(c[:b]) < minv:
            minv = sum(c[:b])

if minv == 50*26:
    print(-1)
else:
    print(minv)
'''

a,b = [int(i) for i in input().split()]
arr = [int(i) for i in input().split()]

c = int(b/a)

d = [0]*100

for i in arr:
    d[i] += 1

sorted(d,key=lambda x:-x)

while c > 0:
    tmp = c
    tmparr = [0]*b
    for _ in range(a):
        flag = False
        for o in range(b):
            if d[o]-tmparr[o] >= c:
                tmparr[o] += c
                flag = True
                break
        if flag == False:
            c -= 1
            break
    if tmp == c:
        break
print(c)