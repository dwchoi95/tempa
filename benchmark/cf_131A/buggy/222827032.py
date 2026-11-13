s = input()
if s.isupper():
    print(s.title())
elif s[0].islower() and len([e for e in s[1::] if e.isupper()]) == len(s)-1:
    print(s.title())
else:
    print(s)