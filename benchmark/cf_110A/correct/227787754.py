a = input()
k = 0
for i in range(len(a)):
    if a[i] in ['4', '7']:
        k += 1
print("YES" if k == 4 or k == 7 else "NO")