n = input()
if n == n.upper() or n[1:len(n)] == n[1:len(n)]:
    ans = n[0].upper() + n[1:len(n)].lower()
print(ans)