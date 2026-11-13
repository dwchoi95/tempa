s = input()
cnt = 0
pr = False
for i in range(len(s)):
    if s[i] == "4" or s[i] == "7":
        cnt += 1
cnt = str(cnt)
for i in range(len(cnt)):
    if cnt[i] != "4" and cnt[i] != "7":
        pr = True
if pr:
    print("NO")
else:
    print("YES")