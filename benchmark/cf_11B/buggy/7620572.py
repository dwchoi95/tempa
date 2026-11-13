import itertools

import time
def timer(f):
    def tmp(*args, **kwargs):
        t = time.time()
        res = f(*args, **kwargs)
        print("Время выполнения функции: %f" % (time.time()-t))
        return res

    return tmp

#n = int(input())

n = abs(int(input()))
i = 1
current = 0
while current+i<=n:
    current+=i
    i+=1

i-=1
i+=2*(n-current)
print(i)