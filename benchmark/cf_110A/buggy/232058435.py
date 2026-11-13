n = int(input())
k = str(n)

lucky = True
for letter in k:
    if letter != '4' or letter != '7':
        lucky = False
        break
    
print("YES" if lucky == True else "NO")