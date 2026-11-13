x = input()
four = 0
seven = 0
for i in range(len(x)):
   if x[i]=="4":
       four+=1
   if x[i]=="7":
       seven+=1 
if four == 0 or seven ==0:
    print("NO")
elif int(four+seven)==len(x):
    print("YES")
else:
    print("NO")