n=set(input())
if len(n)>2:
    print("NO")
else:
    forbid=["1","2","3","5","6","8","9"]
    if any(str(num) in n for num in forbid):
        print("NO")
    else:
        print("YES")