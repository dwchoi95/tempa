x = str(input())
tab = {ord("4"):None,ord("7"):None}
def islucky(x):
    four = x.replace("4","")
    seven = x.replace("7","")
    if len(four) == 0 or len(seven) == 0:
        print("NO")
        return
    x = x.translate(tab)
    if len(x) == 0:
        print("YES")
    else:
        print("NO")
    return
islucky(x)