s=input()
sa=[]
flag=0
if(s[0].islower()):
    sa.append(s[0].upper())
    for i in range(1,len(s)):
          sa.append(s[i].lower())
else:
    for i in range(1,len(s)):
       if(s[i].lower()):
           print(s)
           flag=1
           break
    for i in range(len(s)):
          sa.append(s[i].upper())

if(flag==0):
 print(sa)