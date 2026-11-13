x = input()
count = 0

for i in range(len(x)):
    if (x[i] == "4" or x[i] == "7"):
        count += 1

if (count == 4 or count == 7):
    print("YES")
else:
    print("NO")