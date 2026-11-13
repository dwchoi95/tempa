x=input()
l=[]
e=[]
p=['A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z']
q=['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z']
s=0
r=0
for i in range(len(x)):
    if x[0] in q :
        if i==0 and x[i] in q:
            l.append(p[q.index(x[0])])
            s+=1
        if i!=0 and x[i] in p:
            l.append(q[p.index(x[i])])
            s+=1
            
            
    if x[i] in p:
        e.append(q[p.index(x[i])])
        r+=1
        
if s==len(x):
    print(''.join(l))
if r==len(x):
    print(''.join(e))
if s!=len(x) and r!=len(x):
    print(x)