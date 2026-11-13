s = str(input())  
upp = 0 
low = 0 
for i in range(len(s)):
    if s[i].isupper():
        upp += 1
    else:
        low+=1

if s[0].islower() and upp == len(s)-1 :
    d = s.lower()
    f = d.capitalize()
    print(f)
elif s[0].isupper() and low == len(s)-1:
    d = s 
    print(d)
else:
    print(s)