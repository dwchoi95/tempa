n=input()
lucky_numbers = 0
for i in n:
    if i== "4" :
        lucky_numbers= lucky_numbers+1
    if i == "7":
        lucky_numbers = lucky_numbers + 1
if lucky_numbers == 4 or lucky_numbers==7:
    print("YES")
else:
    print("NO")