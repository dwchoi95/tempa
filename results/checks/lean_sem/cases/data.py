l = [3, 1, 2]
l.sort(); l.insert(0, 9); l.extend((4, 5)); l.remove(9); print(l, l.pop(), l.index(2), l.count(1))
l[1:3] = [7, 8, 9]; del l[0]; print(l, l[::2], l[-2:])
d = {"b": 2, "a": 1}
d["c"] = 3; del d["b"]; print(d, list(d), list(d.items()), d.get("z", 0), d.setdefault("e", 5), d.pop("a"))
print(sorted(d), max(d.values()), {**d, "f": 6}, dict(zip("xy", [1, 2])), dict.fromkeys("ab", 0))
s = {3, 1}; s.add(2); s.discard(5); print(sorted(s), s | {9}, s & {1, 2}, s - {1}, {1} <= s)
t = (1, 2, 2); print(t.count(2), t.index(2), len(t), t[1:])
print(list(enumerate("ab", 1)), list(zip([1, 2], "ab")), list(filter(None, [0, 1, 2])), any([]), all([]))
print(sum([[1], [2]], []), min([3, 1], key=lambda v: -v), round(2.5), round(3.5), round(2.675, 2), abs(-3))
print(list(range(10, 0, -3)), range(5)[2], len(range(0, 10, 3)), 3 in range(5))
m = [[0] * 2 for _ in range(2)]; m[0][1] = 1; print(m)
print(int("  -12 "), int("ff", 16), float("1e3"), bool(""), str(None), tuple("ab"), list({1: 2}))
