#mashup2 
'''
s = input()
d=s[1:]
if (s.upper() == s):
    print(s.lower())

elif (d.upper() == d):
    print(s[0:1].upper(), end = "")
    print(s[1:].lower())
else:
    print(s)


n = int(input())
l = list(map(int,input().split()))
m = int(input())
v=list(map(int,input().split()))
a,b=0,0
d = [0]*(n+1)
for i in range(n) :
	d[l[i]] = i

for q in v:
	a += d[q]+1
	b += n-d[q]
print(a,b)


n=int(input())
s=input()
ss=''
a=set()
if len(set(s))<n:
    print('NO')
else:
     print('YES')
     for i in s:
         if n==0 or i in a:
             ss+=i
         else:
              ss+='\n'+i
              a.add(i)
              n-=1
print(ss)

n=int(input())
r={}
for i in range(n):
    b=input()
    c=0
    o=0
    for i in range(len(b)):
        if(b[i]=="("):o+=1
        else:
            if(o>0): o-=1
            else: c+=1
    if(c==0):
        if(o in r):r[o]+=1
        else: r[o]=1
    elif(o==0):
        if(-c in r): r[-c]+=1
        else:r[-c]=1
t=0
for i in r:
    if(i>=0):
        if(-i in r): t+=r[-i]*r[i]
            
print (t)
'''

from collections import Counter
n, m = list(map(int, input().split()))
f = list(map(int, input().split()))
c = dict(Counter(f))
d = 1
ans = 0
while d:
    t = 0
    for i in c.values():
        t += i//d
    if t >= n:
        ans = d
    else:
        break
    d += 1
print(ans)