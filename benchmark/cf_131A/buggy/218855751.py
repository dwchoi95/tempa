n = input()

count = 0

for i in n:
    if i.isupper():
        count += 1

if count == len(n) or count == len(n) - 1:
    print(n.capitalize())

else:
    print(n)  # no condition is satisfied