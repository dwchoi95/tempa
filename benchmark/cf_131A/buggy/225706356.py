x = str(input())
x = list(x)

for i in range(len(x)):
    x[i] = x[i].lower()
if ("".join(x) == "capslock"):
    print("cAPSlOCK")
else:
    for i in range(len(x)):
        x[0] = x[0].upper()
    print("".join(x))