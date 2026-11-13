s = input()

count = 0
for c in s:
    if c == "4" or c == "7":
        count += 1
print("YES") if count == len(s) else print("NO")