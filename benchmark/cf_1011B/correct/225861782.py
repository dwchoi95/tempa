# LUOGU_RID: 126684742
a,b=map(int,input().split());b=input().split();c={}
for i in b:
    if i in c:c[i]+=1
    else:c[i]=1
b=1
while 1:
    if sum(c[j]//b for j in c)<a:print(b-1);break
    b+=1