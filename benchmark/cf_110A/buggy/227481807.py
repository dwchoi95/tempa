n=int(input())
lst=sorted(list(set(str(n))))
l=['4','7']
if l==lst:
    print("YES")
else:
    print("NO")