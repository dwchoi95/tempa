x = input()
test = 0
for i in range(len(x)):
   if x[i]=="4" or x[i]=="7":
       test+=1
if test==len(x):
    print('YES')
else:
    print("NO")