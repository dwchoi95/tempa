n = input()

cnt = sum([1 if x == "4" or x == "7" else 0 for x in n])

if cnt == 4 or cnt == 7 :
    print("YES")
else :
    print("NO")