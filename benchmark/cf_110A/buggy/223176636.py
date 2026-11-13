m=input()
lst=[]
for a in m:
    lst.append(a)
if "1" in lst or "2" in lst or "3" in lst or "5" in lst or "6" in lst or "8" in lst or "9" in lst or "0" in lst:
    print("NO")
else:
    print("YES")