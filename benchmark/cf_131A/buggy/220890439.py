s=str(input())
if s.isupper():
    string=""
    string+=s[0]
    string+=s[1:].lower()
    print(string)
elif s[0].islower() and s[1:].isupper():
    stringnew=''
    stringnew+=s[0].upper()
    stringnew+=s[1:].lower()
    print(stringnew)
else:
    print(s)