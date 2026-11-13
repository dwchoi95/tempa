s=(input())
length=len(s)
count=0
for i in range(length):
    if s[i]>="A" and s[i]<="Z":
        count=count+1
if count==length or count==length-1:
    if count==length:
        print(s.lower())
    elif count==length-1:
        print(s.capitalize())
else:
    print(s)