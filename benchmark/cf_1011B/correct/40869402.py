[n,m] = [int(i) for i in input().split()]
foods = [0]*101

flag = 0
for i in input().split():
    foods[int(i)] += 1

for d in range(m,0,-1):
    copy = list(foods)
    k = 0
    for i in range(101):
        while copy[i] >= d:
            k += 1
            copy[i] -= d

    if k >= n:
        print(d)
        flag = 1
        break

if not flag:
    print(0)