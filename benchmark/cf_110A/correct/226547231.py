no = input()
count = 0
for each in no:
    if each == "4" or each == "7":
        count += 1
        
if count == 4 or count == 7:
    print("YES")
else:
    print("NO")