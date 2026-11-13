s = input()
ok = True
for i in range(1,len(s)):
    if ord('A') <= ord(s[i]) <= ord('Z'):
        ok = False
if not ok:
    for c in s:
        if ord('a') <= ord(c) <= ord('z'): #小写字母
            print (chr(ord(c)-(ord('a')-ord('A'))),end='')
        else:
            print (chr(ord(c)+(ord('a')-ord('A'))),end='')
else:
    print(s)