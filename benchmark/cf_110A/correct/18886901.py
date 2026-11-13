n = int(input())

t = 0

while n:

    if n % 10 in [4 , 7]:

        t +=1

    n //=10

c = 'YES'

if not t:

    c = 'NO'

while t:

    if t % 10 not in [4 , 7]:

        c = 'NO'

    t //=10

print(c)