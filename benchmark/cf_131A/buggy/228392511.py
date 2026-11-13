a = str(input())
b = str()
b += a[0].upper()
cnt = 0
nec_len = len(a) - 1
first_flag = False
if a[0] != a[0].upper():
    first_flag = True
    nec_len += 1
for i in range(1, len(a)):
    if a[i] == a[i].upper():
        cnt += 1

if ((first_flag == True and cnt == nec_len - 1) or (cnt == nec_len)):
    for i in range(1, len(a)):
        b += (a[i].lower())
    print(b)
else:
    print(a)
# Mon Oct 16 2023 12:25:57 GMT+0300 (Moscow Standard Time)