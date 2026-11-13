a=input()
n=0
d=0
for i in a:
    if ord(i)==65:
        n+=1
    else:
        d+=1
if n>d:
    print('Anton')
elif n==d:
    print('Friendship')
else:
    print('Danik')