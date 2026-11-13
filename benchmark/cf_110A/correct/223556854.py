def is_lucky(n):
    n_set = set(str(n))
    lucky_set = {"4", "7"}
    if n_set - lucky_set:
        return False
    return True


s = input()

lucky_count = 0
for c in ("4", "7"):
    lucky_count += s.count(c)

if lucky_count == 0 or not is_lucky(lucky_count):
    print("NO")
else:
    print("YES")