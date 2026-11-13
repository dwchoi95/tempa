n = input().strip()

count = n.count('4') + n.count('7')

if count == 4 or count == 7:
    print("YES")
else:
    print("NO")