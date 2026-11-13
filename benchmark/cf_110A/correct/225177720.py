n = list(input())
c = list(str(n.count("4") + n.count("7")))
if c.count("4") + c.count("7") == len(c):
    print("YES")
else:
    print("NO")