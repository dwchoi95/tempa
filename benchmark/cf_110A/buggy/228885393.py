s = input()
flag = 0
for i in range(len(s)):
    if i == 4 or i == 7:
        flag = 0
        
        
    else:
        flag = 1
        break
if flag == 0 or (len(s) == 4 or len(s) == 7):
    print("YES")
else:
    print("NO")