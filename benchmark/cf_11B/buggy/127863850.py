def findN(sum):
    i = 0
    num = 0
    while num <= sum:
        num += i
        i += 1
    num -= i - 1
    i -= 2
    if num == sum:
        print(i)
    else:
        diff = sum - num
        print(i + (diff*2))


x = int(input())
findN(x)