n = input()
luck = 0
for i in range(len(n)):
    if n[i] == '4' or n[i] == '7':
        luck += 1
luck = str(luck)
flag = True
for i in luck:
    if i == '4' or i == '7':
        continue
    else:
        flag = False
        break
if flag:
    print("YES")
else:
    print("NO")