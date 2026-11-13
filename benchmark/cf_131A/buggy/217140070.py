x = input()
a = x[0].isupper()
n = 1
for u in x:
    if a != u.isupper():
        n = 0
        break
if n == 1:
    print(x)
if n == 0:
    z = x.lower()
    z = z.capitalize()
    print(z)