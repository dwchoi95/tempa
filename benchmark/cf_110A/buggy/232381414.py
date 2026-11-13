s=input()
mp={}
for i in s:
    if i=='4' or i=='7':
        if i not in mp:
            mp[i]=1
        else:
            mp[i]+=1
print(mp,len(mp))
ans=mp['4']+mp['7']
if ans==4 or ans==7 or ans==47 or ans==74 or ans==447 or ans==474 or ans==477 or ans==744 or ans==747 or ans==774 or ans==777 or ans==444 or ans==7777 or ans==4444 or ans==4447 or ans==4474 or ans==4477 or ans==4744 or ans==4747 or ans==4774 or ans==4777 or ans==7444 or ans==7447 or ans==7474 or ans==7477 or ans==7744 or ans==7747 or ans==7774:   
    print("YES")
else:
    print("NO")