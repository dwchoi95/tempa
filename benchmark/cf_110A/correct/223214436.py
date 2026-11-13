m=input()
lst=[]
for a in m:
    lst.append(a)
p=lst.count("4")
q=lst.count("7")
if p+q==4 or p+q==7:
    print("YES")
else:
    print("NO")