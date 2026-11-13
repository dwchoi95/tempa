def nearlyLuckyNumber():
    n = input()
    nearlyLucky = False
    count47 = 0
    for char in n:
        if char == "4" or char == "7":
            count47 += 1   
            if count47 > 7:
                break
        
    if count47 == 4 or count47 == 7:
        print("YES")
    else:
        print("NO")

nearlyLuckyNumber()