puzzle = input()
lucky = 0
for i in range(len(puzzle)):
  if puzzle[i] == "4" or puzzle[i] == "7":
    lucky += 1
if lucky == len(puzzle):
  print("YES")
else:
  print("NO")