def isLucky(n):

    if(n == 0):

        return False

    while(n > 0):

        if(n % 10 != 4) and (n % 10 != 7):

            return False

        n //= 10

    return True



def noOfLuckyDigits(n):

    count = 0

    while(n > 0):

        if(n % 10 == 4) or (n % 10 == 7):

            count += 1

        n //= 10

    return count



n = int(input())

if(isLucky(noOfLuckyDigits(n))):

    print("YES")

else:

    print("NO")