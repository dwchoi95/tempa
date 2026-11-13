num = abs(int(input()))
l = [int(x) for x in str((num))]
lucky = (str(l.count(4) + l.count(7)))
listed = [y for y in lucky if y!='4' and y!='7']
if len(listed) == 0:
    print("YES")
else:
    print("NO")