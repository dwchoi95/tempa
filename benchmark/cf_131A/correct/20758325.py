s = input()

q = True

for i in s:

    if (i>='A' and i<='Z'):

        continue

    q = False

if (q==True):

    print(s.swapcase())

    exit(0)

q = True

for i in range(1,len(s)):

    if (s[i]>='A' and s[i]<='Z'):

        continue

    q = False

if (q==True):

    print(s.swapcase())

    exit(0)

print(s)