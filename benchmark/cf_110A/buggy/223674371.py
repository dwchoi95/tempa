number = input()
numbers = ['0', '1', '2', '3', '5', '6', '8', '9']

found = True

for digit in number:
    if digit in numbers:
        found = False
        break

if found:
    print("YES")
else:
    print("NO")