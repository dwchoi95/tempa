s = input()

# check if the word satisfies either of the two conditions
if s.isupper() or (s[0].islower() and s[1:].isupper()):
    # if it does, convert the case of all letters
    print(s.swapcase())
else:
    # otherwise, leave the word unchanged
    print(s)