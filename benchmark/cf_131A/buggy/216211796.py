s = input()
up = 0
low = 0
for i in s:
    if i == i.upper():
        up +=1
    else:
        low+=1
if up == 1 :
    print(s)
elif up==len(s)-1:
    print(s.capitalize())
else:
    print(s.lower())