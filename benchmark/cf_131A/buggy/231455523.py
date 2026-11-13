def solve(s):
    if s.upper() == s:
        return s
    return s.capitalize()

s = input()
print(solve(s))