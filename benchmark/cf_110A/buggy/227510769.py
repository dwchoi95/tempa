text = input()
near = True
for dt in text:
    if int(dt) != 7 and int(dt) != 4:
        near = False
if near:
    print("YES")
else:
    print("NO")
quit()