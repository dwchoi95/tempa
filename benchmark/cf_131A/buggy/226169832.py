def def1(x):
    if x.isupper() or x[1:].isupper():
        return x.swapcase()
    else:
        return x

x1 = input().strip()
trans = def1(x1)
print(trans)