def solve(s):
    for i in s:
        if i not in [4,7]:
            return "NO"
    return "YES"

print(solve(input()))