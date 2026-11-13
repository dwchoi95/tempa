n, m = map(int, input().split())
l = [int(x) for x in input().split()]

dict = {}

for x in l:
    try:
        dict[x] = dict[x] + 1
    except:
        dict[x] = 1


for i in range(1,110):
    t = 0
    for k in dict:
        t += dict[k]//i

    if t<n:
        print(i-1)
        break