num = input()
x = 0 # number of lucky numbers

for char in num:
    if char == "4" or char == "7":
        x += 1
        
if x == 4 or x == 7:
    print("YES")
else:
    print("NO")