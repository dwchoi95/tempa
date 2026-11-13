def isLucky(num):
    num = str(num)
    LuckyCount = 0
    for i in range(0, len(num)):
        if (num[i] == "4" or num[i] == "7"):
            LuckyCount += 1

    return "YES" if LuckyCount == 7 or LuckyCount == 4 else "NO"

print(isLucky(input()))