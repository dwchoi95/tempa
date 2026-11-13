n = input()

lucky = True
nearly_luckly = True

count = 0


for x in str(len(n)):
    if x == "4" or x == "7":
        count += 1
for x in str(count):
    if x != 4 and x != 7:
        nearly_lucky = False

if nearly_lucky == True:
    print("Yes")
else:
    print("NO")