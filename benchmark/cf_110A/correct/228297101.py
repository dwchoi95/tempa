n = input()
luc = 0
for x in n:
    if x == '4' or x == '7':
        luc+=1
if luc ==4 or luc == 7:
    print("YES")
else:
    print("NO")