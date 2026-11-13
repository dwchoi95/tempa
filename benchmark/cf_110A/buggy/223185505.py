def isLucky(num):
    num = str(num)
    Lucky = "YES"
    for i in range(0, len(num)):
        if not (num[i] == "4" or num[i] == "7"):
            Lucky = "NO"
            break

    return Lucky

print(isLucky(input()))