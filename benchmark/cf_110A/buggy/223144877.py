def nearlyLucky(money):
    count = 0

    while money > 0:
        if money % 10 == 4 or money % 10 == 7:
            count += 1
        money //= 10

    return count in ( 4 ,7)
if __name__ == "__main__":
    money = int(input())
    print ("yes" if nearlyLucky(money) else "no")