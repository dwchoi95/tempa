s=input()
up=s.upper()
if s[1:len(s)]==up[1:len(s)]:
    print(s.capitalize())
else:
    print(s)