n = input()


nearly_luckly = True

count = len(n)


for x in str(len(n)):
    if x != "4" and x != "7":
        count -= 1
count = str(count)
for x in count:
    if x != "4" and x != "7":
        nearly_luckly = False

if nearly_luckly == True:
    print("YES")
else:
    print("NO")