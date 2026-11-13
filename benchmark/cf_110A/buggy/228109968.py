number = input()
count = 0
yes = 1
for d in number:
    if d == "4" or d == "7":
        count += 1
print(count)
for d2 in str(count):
    if d2 != "4" and d2 != "7":
        print("NO")
        yes = 0
        break
if yes == 1:
    print("YES")