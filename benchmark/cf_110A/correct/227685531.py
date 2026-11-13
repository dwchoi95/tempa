from collections import *
n = input()
val1 = n.count("4")
val2 = n.count("7")
ans = str(val1 + val2)

for i in str(ans):
    if i not in "47":
        print("NO")
        break
else:
    print("YES")