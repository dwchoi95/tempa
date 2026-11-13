n = input()

count = 0

count += n.count("4")
count += n.count("7")

if count == 7 or count == 4:
	print("YES")
else:
	print("NO")