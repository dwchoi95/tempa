n = int(input())
n_str = str(n)
count = 0
for digit in n_str:
    if (digit == "4" or digit == "7"):
        count += 1
if all(d == '4' or d== '7' for d in str(count)):
    print("YES")
else:
    print("NO")