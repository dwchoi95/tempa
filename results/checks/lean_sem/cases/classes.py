class A:
    k = 1
    def __init__(self, x):
        self.x = x
    def get(self): return self.x + self.k
    def __repr__(self): return "A(%d)" % self.x
    def __eq__(self, o): return isinstance(o, A) and o.x == self.x
    def __lt__(self, o): return self.x < o.x
    def __add__(self, o): return A(self.x + o.x)
    def __len__(self): return self.x
    @staticmethod
    def st(v): return v * 2
    @classmethod
    def cm(cls): return cls.k
    @property
    def p(self): return self.x * 10
class B(A):
    k = 5
    def get(self): return A.get(self) * 100
a, b = A(1), B(2)
print(a.get(), b.get(), a, [b, a], sorted([b, a]), a == A(1), a + b, len(b), bool(A(0)))
print(A.st(3), B.cm(), a.p, isinstance(b, A), issubclass(B, A), type(b).__name__, B.__mro__ if False else B.__name__)
class C:
    def __init__(self): self.items = [3, 1]
    def __iter__(self): return iter(self.items)
    def __getitem__(self, i): return self.items[i]
    def __str__(self): return "C!"
c = C()
print(list(c), c[0], str(c), f"{c}")
print(C.__qualname__, A.__module__)
def mk():
    class D: pass
    return D
print(mk().__qualname__)
