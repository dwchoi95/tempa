a = b = [1]
a += [2]
print(b)
t = (1,)
u = t
t += (2,)
print(u, t)
d = {"k": [1]}
def key():
    print("key"); return "k"
d[key()] += [5]
print(d)
class O: pass
o = O(); o.n = 1
o.n *= 10
print(o.n)
s = "ab"; s *= 3; print(s)
n = 7; n //= 2; n **= 3; n %= 5; n <<= 2; n |= 1; n ^= 3; n &= 6; n >>= 1; print(n)
