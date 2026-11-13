n = str(input())
count = 0
for i in range(len(n)):
    if n[i] == '4' or n[i] == '7':
        count+=1
if count == len(n):
    print("YES")
else:
    print("NO")