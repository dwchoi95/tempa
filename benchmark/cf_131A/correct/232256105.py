a=str(input())
s=0
output=str()
for i in range(1, len(a)):
    if a[i].isupper():
        continue
    else:
        print(a)
        break
else:
    for i in range(len(a)):
        if a[i].isupper():
            output+=a[i].lower()
        else:
            output+=a[i].upper()
    print(output)