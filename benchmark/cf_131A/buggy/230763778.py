a = list(str(input()))
for i in range(len(a)):
    if i!=0:
        a[i] = a[i].lower()
    else:
        a[i] = a[i].upper()
for elt in a:
    print(elt, end="")