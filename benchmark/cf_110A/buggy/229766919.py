x = str(input())
def islucky(x):
    for char in x:
        print("-",char,type(char))
        if char != "4" and char != "7":
            print("NO")
            return
    print("YES")
    return
islucky(x)