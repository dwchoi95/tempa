n = int(input())
num = str(n)
ln = len(num)
count = 0
i = 0
while i < ln:
    if num[i] == "7" or num[i] == "4":
        count = count + 1
    i = i + 1
if count == ln:
    print("YES")
else:
    print("NO")