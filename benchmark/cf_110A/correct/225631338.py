arr = list(input())
total = arr.count("4") + arr.count("7")
if total == 4 or total == 7:
    print("YES")
else:
    print("NO")