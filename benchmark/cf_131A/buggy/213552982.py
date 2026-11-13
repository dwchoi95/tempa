k = input().strip()

if k.isupper() or k[1:].isupper():
    print(k.swapcase())
else:
    print(k)