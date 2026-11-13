s = "Hello World"
print(s.upper(), s.lower(), s.swapcase(), s.title(), s.capitalize(), s.isupper(), s.istitle())
print(s.split(), "a,b,,c".split(","), "  x  ".strip(), s.count("o"), s.find("W"), s.replace("l", "L", 2))
print("-".join(["a", "b"]), s[::-1], s[1:4], s[-1], "abc".index("c"), s.startswith("He"), "x".zfill(3))
print("%5.2f|%-4d|%s|%r|%x|%03d" % (3.14159, 7, "s", "r", 255, 5))
print("{} {:>6} {:.3f} {:,} {:08.2f} {name}".format(1, "ab", 2.0, 1234567, -3.5, name="n"))
x = 42
print(f"{x} {x:5d} {x!r} {x / 7:.4} {'q'!r:>5} {x:#x} {x:b}")
print(str(1.5), repr("it's"), repr('say "hi"'), ord("a"), chr(65), "aBc".casefold())
print(" ".join(reversed("abc")), sorted("cba"), list(map(int, "1 2 3".split())), "a b".partition(" "))
