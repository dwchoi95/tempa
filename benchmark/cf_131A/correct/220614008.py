s = str(input())
upp = 0
low = 0
for i in s:
    if i.islower():
        low+=1
    else:
        upp+=1
if s[0].islower() and upp == len(s)-1:
    for i in range(len(s)):
        if i==0:
            print(s[i].upper(),end="")
        else:
            print(s[i].lower(),end="")
elif upp == len(s):
    for i in range(len(s)):
        print(s[i].lower(), end="")
else:
    print(s)