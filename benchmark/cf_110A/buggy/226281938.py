x = input()

for char in x:
    if char not in ('4', '7'):
        print("NO")
        break
else:
    print("YES")