string = str(input().lower())
ans = ''

ans += string[0].upper()
for i in range(1, len(string)):
   ans += string[i]

print(ans)