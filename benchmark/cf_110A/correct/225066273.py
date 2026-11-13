value = input()
total = str(value.count("4") + value.count("7"))
if len(total) == (total.count("4") + total.count("7")):
    print("YES")
else:
    print("NO")