number=list(input())
n=0
for digit in number:
    if digit=="4" or digit=="7":
        n+=1
num=list(str(n))
while "4" in num:
    num.remove("4")
while "7" in num:
    num.remove("7")
if num==[]:
    print("YES")
else:
    print("NO")