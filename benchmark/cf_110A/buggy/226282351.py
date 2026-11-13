x = input()

if all(char in ('4', '7') for char in x) and '4' in x and '7' in x:
    print("YES")
else:
    print("NO")