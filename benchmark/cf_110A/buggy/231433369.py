def isLuckyNum(s):
    for ch in s:
        if ch not in ['4','7']:
            return "NO"
    return "YES"
s = input()
print(isLuckyNum(s))