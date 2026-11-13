s=input()
if s.isupper():
    s=s.lower()
    s=s.capitalize() 
else:
    if s[0].islower() and s[1].isupper:
        s=s.lower()
        s=s.capitalize()
        
print(s)