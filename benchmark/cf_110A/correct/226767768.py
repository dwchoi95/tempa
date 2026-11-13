num=input()
count=0
for i in range (len(num)):
    if ord(num[i])==52 or ord(num[i])==55:
        count+=1
count=str(count)
i=0
while (i<len(count)):
    if ord(count[i])!=52 and ord(count[i])!=55:
        print("NO")
        break
    i+=1
    if i==len(count):
        print("YES")