n=int(input())
def fun(n):
    st=str(n)
    for i in st:
        if i!='4' and i!='7':
            return False
    return True
if fun(n):
    print("YES")
else:
    print("NO")