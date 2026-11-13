n = input()

set_n = set(n)
 
total = 0
new_list = []

for i in list(set_n):
    if i == "4":
        new_list.append(i)
    elif i == "7":
        new_list.append(i)
    else:
        total += 1
        
if (total == 0) and (len(new_list) == 2):
    print("YES")
else:
    print("NO")