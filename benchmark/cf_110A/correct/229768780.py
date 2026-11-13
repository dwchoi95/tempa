x = str(input())
def isnearlucky(x):
    count = 0
    for char in x:
        if char == "4" or char == "7":
            count += 1
            continue
    count = str(count)
    count = count.replace("4","")
    count = count.replace("7","")
    if len(count) == 0:
        print("YES")
    else:
        print("NO")
isnearlucky(x)