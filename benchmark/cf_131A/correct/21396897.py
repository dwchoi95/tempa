s = input()

one = s[0]

ends = s[1:]



if len(s) == 1:

    s = s.swapcase()

else:

    if one.islower() and ends.isupper():

        s = s.capitalize()

    elif s.isupper():

        s = s.lower()

print(s)