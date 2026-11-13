n = int(input())

s = set([i for i in str(n)])

if s != {3,7}:
    x = 0
    for i in str(n):
        if i == "4" or i =="7":
            x+=1
    if x != 7 or x != 4:
        print("No")
    else: print("YES")
else: print("No")