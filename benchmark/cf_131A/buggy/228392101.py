a = str(input())
b = str()
b += a[0].upper()
cnt = 0
first_flag = False
if a[0] != a[0].upper():
    first_flag = True
for i in range(1, len(a)):
    if a[i] == a[i].upper():
        cnt += 1

if ((first_flag == True and cnt == len(a)-1) or (cnt == len(a))):
    for i in range(1, len(a)):
        b += (a[i].lower())
    print(b)
else:
    print(a)
# Mon Oct 16 2023 12:21:45 GMT+0300 (Moscow Standard Time)