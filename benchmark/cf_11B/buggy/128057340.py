def findN(sumNum):
    i = 0
    num = 0
    if sumNum < 0:
        sumNum = -sumNum
    while num <= sumNum:
        num += i
        i += 1
    num -= i - 1
    i -= 2
    if num == sumNum:
        print(i)
    else:
        diff = sumNum - num
        if diff == 1:
            print(i + 2)
        else:
            print(i + 1 + 2)


x = int(input())
findN(x)