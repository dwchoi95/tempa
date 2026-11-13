n = input()

# count the number of lucky digits
count = sum(1 for c in n if c in "47")

# check if the count is a lucky number
if count in [4, 7]:
    print("YES")
else:
    print("NO")