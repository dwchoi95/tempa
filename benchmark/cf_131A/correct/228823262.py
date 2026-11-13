s = str(input())
uppercase_test = 0
x = 0

for i in range(len(s)):
    if ord(s[i])>=65 and ord(s[i])<=90:
        uppercase_test += 1
for i in range(1,len(s)):
    if ord(s[i])>=65 and ord(s[i])<=90:
        x +=1

if (ord(s[0])>=97 and ord(s[0])<=122) and x== len(s)-1 :
    print(str(s[0]).upper()+str(s[1:]).lower())
elif uppercase_test == len(s):
    print(str(s.lower()))
else:
    print(s)