number = input()
x = list(set([int(i) for i in number]))
if x != [4,7]:
    print("NO")
else:
    print("YES")