n = int(input())
str_n = str(n)
res = False

for i in range(len(str_n)):
    if str_n[i] == '4' or str_n[i] == '7':
        res = True
    else:
        res = False
        break  # Exit the loop as soon as a non-lucky digit is encountered

if res:
    print("YES")
else:
    print("NO")