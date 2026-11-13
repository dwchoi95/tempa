x = str(input())
x = list(x)
for i in range(len(x)):
    x[i] = x[i].lower()
    x[0] = x[0].upper()
print("".join(x))