from itertools import groupby

n, k = [int(x) for x in input().split()]
values = [int(x) for x in input().split()]

result = 0
if n > k:
    pass
elif n == k:
    result = 1
else:
    values = sorted(values)
    max_days = k // n
    while max_days:
        humans = n
        count = 0
        current_item = None
        for _, items in groupby(values):
            l = len(list(items))

            humans -= max(l // max_days, 0)
        if humans == 0:
            break
        else:
            max_days -= 1
    result = max_days
print(result)