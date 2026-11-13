n = input()  # Input: The integer n as a string

lucky_count = n.count('4') + n.count('7')

if lucky_count in {4, 7}:
    print("YES")
else:
    print("NO")