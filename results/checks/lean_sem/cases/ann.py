if False:
    z: int = 0
x: int = 5
y: "str"
class C:
    a: int = 1
    b: str
print(__annotations__, C.__annotations__, x)
def f():
    v: int = 3
    w: undefined_name
    return v
print(f())
