n = input()
ans = "NO"
for i in range(len(n)):
    if n[i] == "4" or n[i] == "7":
        ans = "YES"
    else:
        ans = "NO"
        break
print(ans)