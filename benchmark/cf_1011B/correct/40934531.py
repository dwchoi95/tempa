def f(p, k):
  if k == 0:
    return 0
  s = 0
  for i in p:
    s = s + i // k
  return s
n, m = [int(x) for x in input().split()]
packages = [int(x) for x in input().split()]
q = 101*[0]
for i in packages:
  q[i] = q[i] + 1
q = sorted(q, reverse=True)
packages = []
for i in q:
  if i > 0:
    packages.append(i)
l = 1
r = m // n + 1
mid = 0
while l < r - 1:
  mid = (l + r) // 2
  if f(packages, mid) >= n:
    l = mid
  else:
    r = mid
if f(packages, r) >= n:
  print(r)
elif f(packages, mid) >= n:
  print(mid)
elif f(packages, l) >= n:
  print(l)
else:
  print('0')