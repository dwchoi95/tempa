n = input()
ans = n
if n == n.upper():
    ans = n.lower()
elif n[1:len(n)] == n[1:len(n)].upper():
    ans = n[0].upper() + n[1:len(n)].lower()
print(ans)