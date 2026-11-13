def t(v): print("t", v); return v
print(t(1) < t(2) < t(0), t(3) == 3 > t(1))
print(t(0) and t(1), t(2) or t(3), not t([]))
print(t(1) if t(None) else t(2))
print(7 // -2, -7 % 3, 2 ** -1, 10 / 4, 7.5 // 2, -7.5 % 2, divmod(-9, 4))
print(1 == 1.0, True + True, 3 * "ab", [1, 2] * 2, (1,) + (2,), 1 < 2.5, "a" < "b")
print(5 & 3, 5 | 3, 5 ^ 3, ~5, 1 << 70, -(2 ** 64) >> 3)
print(1 in [1, 2], "b" in "abc", 3 not in {1: 2}, None is None, [] is not [])
print(0.1 + 0.2, 1e16, 1e-5, 123.456, 2 / 3, float("inf"), -0.0, 1e22, 3.0)
