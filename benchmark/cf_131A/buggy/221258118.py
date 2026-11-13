#Two use cases:
#1: contains only capital letter
#2: all letters except for the first one are capital

#In these two use ccases we change the case of all the letters 

s = input()
if s.isupper():
    print(s[0] + s[1:].lower())
elif s[1:].isupper():
    print(s[0].upper() + s[1:].lower())
else:
    print(s)