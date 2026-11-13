inp=input()
st1=''
st2=''
for i in inp:
  if len(inp)>1:
    if i=="4":
        st1+=i
    elif i =="7":
        st2+=i
if len(inp)==(len(st1))+(len(st2)) or (len(st1))+(len(st2))>3 :
  print("YES")
else:
  print("NO")