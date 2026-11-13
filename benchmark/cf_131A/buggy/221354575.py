def f(n):
    if n.islower() or n.isupper() or (n[0].islower() and n[1:].isupper()):
        return n.swapcase()
    return n
n=input()
s=f(n)
print(s)