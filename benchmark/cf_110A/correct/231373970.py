num = input()
count = 0
vrdct = None
for i in num:
    if i == '4' or i == '7':
        count+=1
vrdct = True if count == 4 or count == 7 else False
if vrdct:
    print("YES")
else:
    print("NO")