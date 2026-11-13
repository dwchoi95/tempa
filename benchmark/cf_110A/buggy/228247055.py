n = input()
X = 0

for i in n:
    if i == '4':
        X += 1
    elif i == '7':
        X += 1
    else:
        X = X

for i in str(X):
    if i == '4' or i == '7':
        print("YES")
    else:
        print("NO")