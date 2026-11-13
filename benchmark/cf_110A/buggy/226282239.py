x = input()

if all(char in ('4', '7') for char in x):
    print("YES")
else:
    print("NO")