n, m =  map(int, input().split())
flst = map(int, input().split())

if m<n:
    print(0)
    exit()

tot = {}

for i in flst:
    tot[i] = tot.get(i, 0) + 1

lst = []

for j in tot:
    lst.append(tot[j])

i = lst.index(max(lst))
j = lst.index(min(lst))
while lst[i] > lst[j]:
    i = lst.index(max(lst))
    j = lst.index(min(lst))
    lst[i] -= 1
    lst[j] += 1

print(min(lst))