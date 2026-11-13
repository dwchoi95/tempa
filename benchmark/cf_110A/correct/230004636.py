x = input("")
luck = 0
for a in x:
    if int(a) == 4 or int(a) == 7:
        luck = luck + 1 

for a in str(luck):
    if int(a) == 4 or int(a) == 7:
        continue
    else:
        print("NO")
        exit()
        
print("YES")