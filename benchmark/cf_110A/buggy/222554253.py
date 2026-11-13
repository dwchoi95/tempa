n = int(input())
s = str(n)
flag =1
count = 0
for i in s:
    if i != '4' and i !='7':
        flag = 0
    else:
        flag =1
    if flag == 1:
       count = count +1
if count == len(s):
    print("YES")
else:
    print("NO")