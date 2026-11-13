number = str(input())
counter = 0
for i in range(len(number)):
    if number[i] == "4" or number[i] == "7":
        continue
    else:
        counter=1
        break

if counter!=0:
    print("NO")
else:
    print("YES")