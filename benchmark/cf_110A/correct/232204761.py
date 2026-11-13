a=input()
length = len(a)
j=0
count = 0
while j < length:
    if ord(a[j])== 52 or ord(a[j]) == 55:
        count += 1
    j+=1
if count == 4 or count == 7:
    print("YES")
else:
    print("NO")