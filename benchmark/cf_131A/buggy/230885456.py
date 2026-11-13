s=input()
c=s[0]
cur=''
for i in range(1,len(s)):
    cur+=s[i]
if (cur==cur.lower() and c==c.lower()):
    ans=c+cur
    print(ans)
else:
    ans=c.upper()+cur.lower()
    print(ans)







# Wed Nov 01 2023 22:53:09 GMT+0300 (Moscow Standard Time)