def isLucky(s):
    s = str(s)
    for i in range(len(s)):
        if s[i] != "4" and s[i] != "7":
            return False
    return True


a = input()
cnt = a.count("4") + a.count("7")
if isLucky(cnt):
    print("YES")
else:
    print("NO")