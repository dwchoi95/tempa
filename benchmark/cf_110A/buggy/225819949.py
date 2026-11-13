t = input()
count_4 = t.count("4")
count_7 = t.count("7")

if count_4 > 0 and count_7 > 0 and count_4 + count_7 == len(t):
    print("YES")
else:
    print("NO")