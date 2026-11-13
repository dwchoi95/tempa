n=input()
n=list(n)
s = 0

for i in n:
    if i == "7" or i == "4":
        s += 1

# Check if the count of lucky digits (4 or 7) is a lucky number (4 or 7)
if s ==len(n) :
    print("YES")
else:
    print("NO")