inp=input()
st1=''
st2=''
for i in inp:
  if len(inp)>1:
    if i=="4":
        st1+=i
    elif i =="7":
        st2+=i
a=len(st1)+len(st2)
if len(inp)==a or a==7 or a==4:
  print("YES")
else:
  print("NO")