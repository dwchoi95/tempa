s = list(input())

caps = True

for i in range(1,len(s)):

    if not ord('A') <= ord(s[i]) <= ord('Z'):

        caps = False



if caps:

    if ord('A') <= ord(s[0]) <= ord('Z'):

        s[0] = chr(ord(s[0]) + 32)

    else:

        s[0] = chr(ord(s[0]) - 32)

    for i in range(1,len(s)):

        s[i] = chr(ord(s[i]) + 32)



print(''.join(s))