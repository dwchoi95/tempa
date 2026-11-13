n = input(" Enter the number: ")
four = n.count('4')
seven = n.count('7')
sum = four + seven
st = str(sum)

result = 1
for i in range (len(st)):
    if (st[i] != '4') and (st[i] !='7'):
        result = 0
        break
if result:
    print("Yes")
else:
    print