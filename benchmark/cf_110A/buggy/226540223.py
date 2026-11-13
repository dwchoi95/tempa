pos  = str(input())

pos = set(pos)

if len(pos) == 2 and ("4" in pos or "7" in pos):
    print("YES")
else:
    print("NO")