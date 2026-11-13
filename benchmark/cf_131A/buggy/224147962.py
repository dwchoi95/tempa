s = str(input())
if s[1::].isupper() or s.isupper():
    print(s.capitalize())
else:
    print(s)