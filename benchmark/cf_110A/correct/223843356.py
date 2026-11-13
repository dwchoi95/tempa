s=input()
a=list(s)
b=a.count('4')+a.count('7')
if b==4 or b==7:
    print("YES")
else:
    print("NO")