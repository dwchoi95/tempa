n=input()
total7=n.count('7')
total4=n.count('4')

if(total7!=0 and total4!=0) and (total7+total4==len(n)):
    print("YES")
else:
    print("NO")