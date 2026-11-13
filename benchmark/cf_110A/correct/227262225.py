a = input()
cnt = 0
cnt += a.count("4")
cnt += a.count("7")
cnt = str(cnt)
f = True
for i in range(len(cnt)):
    if cnt[i] != "4" and cnt[i] != "7":
        f = False
if f:
    print("YES")
else:
    print("NO")