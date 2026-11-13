text = input()
seven = 0
four = 0
for dt in text:
    if dt == "7":
        seven += 1
    if dt == "4":
        four += 1

lns = seven + four
if lns == 4 or lns == 7: 
    print("YES")
else:
    print("NO")
quit()