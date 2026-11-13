n = input()
a=sum(1 for i in n if i in '47')
if a == 4 or a == 7:
    print("YES")
else:
    print("NO")