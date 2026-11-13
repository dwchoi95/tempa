from collections import *
n,m = [int(x) for x in input().split()]
a = [int(x) for x in input().split()]
cnt = Counter(a)
# print(cnt)
#binary search the number of days
lo,hi = 0,m #obviously at most m days, as we have m food in total and at least 1 person
while lo < hi:
    mid = (lo+hi+1)//2 #+1 is necessary due to -1 in line 17
    total = 0
    for val,supply in cnt.items():
        total += supply//mid #each person needs exactly m units of the same type of food
    #total is the total number of people we managed to support with m units
    if total >= n: #managed to support all the people
        lo = mid
    else:
        hi = mid-1
print(lo)