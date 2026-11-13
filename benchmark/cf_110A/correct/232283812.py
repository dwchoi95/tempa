n = int(input())
num = str(n)
ln = len(num)
i = 0
count = 0
while i < ln:
    if num[i] == "4" or num[i] == "7":
        count += 1
    i += 1
if count == 4 or count == 7:
    print("YES")
else:
    print("NO")