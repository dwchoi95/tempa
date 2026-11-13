s = input()
res = ''
for i in s:
    if i == "4" or i == "7":
        res = res + i
    
if len(res) == len(s):
    print("YES")

else:
    print("NO")