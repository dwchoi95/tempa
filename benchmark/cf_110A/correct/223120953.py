a = input()
ns = 0
for char in a:
    if char == '4' or char == '7':
        ns += 1
if ns==4 or ns==7:
    print ("YES")
else:
    print("NO")