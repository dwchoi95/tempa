"""
First we need to check whether the number
contains only the digits 4 and 7.

Next, we need to determine whether the 
length of the string is 4 or 7.

If both of these conditions are met,
the output is YES. Else, NO.
"""

input = input()
listOfNumbers = list(input)

output = ""


def nearlyLucky():
    for i in range(len(input)):
        if listOfNumbers[i] != "4" and listOfNumbers[i] != "7":
            return "NO"

    return "YES"


# Whether string is nearly lucky: 4 or 7

"""
Only if the length of the string is nearly lucky,
as defined as a 4 or a 7, then we will check to
see if any of the digits are 4 or 7 by running
the nearlyLucky() function. Else, we just print NO.
"""
if len(input) == 4 or len(input) == 7:
    output = nearlyLucky()
else:
    print("NO")


# Outputs the right answer, hopefully.
print(output)