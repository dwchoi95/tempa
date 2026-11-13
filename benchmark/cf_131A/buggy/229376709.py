s = input()
count = 0
s1 = 'ABCDEFGHUJKLMNOPQRSTUVWXYZ'
for i in range(len(s)):
    if s[i] in s1:
        count+=1
if count == len(s):
    print(s.lower().title())
elif s[0] not in s1 and count == len(s)-1:
    print(s.lower().title())
else:
    print(s)