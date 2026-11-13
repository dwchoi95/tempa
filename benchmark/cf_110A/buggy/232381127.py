s=input()
mp={}
for i in s:
    if i=='4' or i=='7':
        if i not in mp:
            mp[i]=1
        else:
            mp[i]+=1
print(mp,len(mp))
if mp['4']+mp['7']==4 or mp['4']+mp['7']==7:   
    print("YES")
else:
    print("NO")