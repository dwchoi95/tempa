import sys
# sys.stdin = open("input.txt", "r")
# sys.stdout = open("output.txt", "w")
# sys.stderr = open("error.txt", "w")
# # your remaining code

n =input()

c47= 0

for i in n:
	if i == '4' or i == '7':
		c47+=1

if c47 == 4 or c47 == 7:
	print("YES")
else :
	print("NO")