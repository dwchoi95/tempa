num = input()

lucky = True

for l in num:
    if l != '7' and l != '4':
        lucky = False
        break
    
if(lucky):
    print("YES")
else:
    print("NO")