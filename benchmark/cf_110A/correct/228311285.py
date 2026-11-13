n = input()
count = 0
for i in n:
    if (i == '4') or (i == '7'):
        count+=1
# print(str(count))
flag=0
# print(str(count))
for j in str(count):
    
    if (j=='4') or (j=='7'):
        flag=0
    else:
        flag=1
# print(flag)
if flag==0:
    print("YES")
else:
    print("NO")