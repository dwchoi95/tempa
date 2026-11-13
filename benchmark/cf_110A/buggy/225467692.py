lis = list(input(""))
i = len(lis) - 1
while i > 0:
   if lis[i] != "4" and lis[i] != "7":
     print("NO")
     exit()
   i -= 1
if "4" not in lis or "7" not in lis:
  print("NO")
else:
  print("YES")