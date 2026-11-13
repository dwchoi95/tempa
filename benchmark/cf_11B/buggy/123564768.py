x = int(input())
if (x < 0):
    x = -x
if (x == 0):
    print(0)
s = 0
j = 1
y = 0

while (s<x):
    y=y+1;
    s = s+j
    j=j+1

diff = s-x

if(diff % 2 == 0):
    print(y)
elif((diff + j) % 2 == 0):
    print(y+1)
else:
    print(y+2)