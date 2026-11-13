num = input()
lucky_count = 0
said_no = False

for i in range(len(num)):
    if (int(num[i]) == 4) or (int(num[i]) == 7):
        lucky_count += 1
    else:
        print ("NO")
        said_no = True
        break
        
str_count = str(lucky_count)
for i in range(len(str_count)):
    if said_no == True:
        break
    elif (int(str_count[i]) == 4) or (int(str_count[i]) == 7):
        print("YES")
    else:
        print ("NO")
        break