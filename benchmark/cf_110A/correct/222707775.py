list1 = list(input())

num = list1.count("4") + list1.count("7")
list2 =list(str(num))

result = True
for ch in list2:
    if ch != "4" and ch != "7":
        result = False
        
if result == False:
    print("NO")
else:
    print("YES")