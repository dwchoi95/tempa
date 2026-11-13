in_str = input()
cntr = 0

if (len(in_str) < 1) or (len(in_str) > 18):
    print("Error_1")

for ch in in_str:
    if (ch == '4') or (ch == '7'):
        cntr +=1

if (cntr == 4) or (cntr == 7):
    print("YES")
else:
    print("NO")