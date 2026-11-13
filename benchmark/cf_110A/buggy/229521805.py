x = input()

if any(digit in x for digit in "01235689"):
    print("NO")
else:
    print("YES")