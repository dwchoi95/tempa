def nearlyLuckyNumber():
    n = int(input())
    n = str(n)
    notLucky = True
    if notLucky:
        for char in n:
            if char != "4" and char != "7":
                notLucky = False
        
    if notLucky:
        print("YES")
    else:
        print("NO")

nearlyLuckyNumber()