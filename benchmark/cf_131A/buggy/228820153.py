s = str(input())
uppercase_test = 0
uppercase_except_1 = 0

for i in range(len(s)):
    if ord(s[i])>=65 and ord(s[i])<=90:
        uppercase_test += 1
for i in range(1,len(s)):
    if ord(s[i])>=65 and ord(s[i])<=90:
        uppercase_except_1 += 1

if uppercase_except_1 == len(s)-1:
    print(str(s[0]).upper()+str(s[1:]).lower())
elif uppercase_test == len(s):
    print(str(s[0]).upper()+str(s[1:]).lower())
else:
    print(s)