s = input()
count = 0
for i in range(len(s)):
    if s[i] == "4" or s[i] == "7":
        count += 1
count = str(count)
lucky = True
for ch in count:
    if ch == "4" or ch == "7":
        continue
    else:
        lucky = False
        print("NO")
        break
if lucky:
    print("YES")