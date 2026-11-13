"""
First we need to check whether the
number of times 7 and 4 show up in
the number.

Add the appearances of these numbers
together in a sum. If that sum is
divisible by 4 or 7, then we return
a YES because the number is Nearly
Lucky.

Else, we return a NO.
"""

input = input()
listOfNumbers = list(input)


def nearlyLucky():

    numberof7 = listOfNumbers.count("7")
    print(numberof7)
    numberof4 = listOfNumbers.count("4")
    print(numberof4)
    luckySum = numberof7 + numberof4
    if luckySum % 4 == 0 or luckySum % 7 == 0:
        return "YES"
    else:
        return "NO"


output = nearlyLucky()


# Outputs the right answer, hopefully.
print(output)