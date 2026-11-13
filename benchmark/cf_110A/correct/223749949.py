number = input()
numbers = ["4","7"]

count = 0

for digit in number:
    if digit in numbers:
        count +=1
        

if count == 4 or count ==7:
    print("YES")
else:
    print("NO")