"""n,k = map(int,input().split())
vec = list(map(int,input().split()))
temp = sorted(vec)
temp[n-1],temp[k-1] = temp[k-1],temp[n-1]
if k < n:
    temp[k:] = sorted(temp[k:])
ans = 0
for i in range(n):
    j = 0
    print("Before:",j)
    for j in range(i,n):
        if(temp[i] == vec[j]):
            break
    if(i == j):
        continue
    if(i == 0):
        ans += vec[i]*vec[j]
        vec[i],vec[j] = vec[j],vec[i]
        continue
    ans += 2*min(vec[i],vec[j])*temp[0]+max(vec[i],vec[j])*temp[0]
    vec[i],vec[j] = vec[j],vec[i]
    print("After:",j)
    print("i;",i)
print(ans)

#Code force problem 2
n=int(input())
words = []
for i in range(n):
    words.append(input())
for i in words:
    if len(i)>10:
        print(i[0]+str(len(i)-2)+i[-1])
    else:
        print(i)


#codeforce pb3
n=int(input())
res=0
for i in range(n):
    a=input()
    if a.count('1') >=2:
       res+=1

print(res)

 #codeforce pb4

noPac,kthPl = map(int,input().split())
List = list(map(int,input().split()))

print(sum( i >= List[kthPl-1] and i>0 for i in List))
##for i in List:
##    if i >= List[kthPl]:
##        s+=1
##
##print(s)

 #codeforce pb5
n=int(input())
s=0
##print((List.count('++X') or List.count('X++')) - (List.count('--X') or List.count('X--')))
for i in range(n):
    r=input()
    if '+' in r:
        s+=1
    elif '-' in r:
        s-=1

print(s)

 #codeforce pb6
m,n=map(int,input().split())
print(m*n//2)



#pb 7
List = list(list(map(int,input().split())) for i in  range(5))

r,c= 0,0
for i in range(5):
    if 1 in List[i]:
        r,c = i+1,List[i].index(1)+1
print(abs(3-r)+abs(3-c))


#pb 8
str1 = input()
str2 = input()

if str1.lower() < str2.lower():
    print("-1")
elif str2.lower() < str1.lower():
    print("1")
else:
    print("0")


#pb 10
n = input()
if(n[0].isupper()):
    print(n)
else:
    n=n[0].upper()+n[1:]
    print(n)

#pb 11
n=input()
newn = ''
for i in n:
    if i not in newn:
        newn+=i
if(len(newn)%2==0):
    print("CHAT WITH HER!")
else:
    print('IGNORE HIM!')


#pb BOB

l,b = map(int,input().split())
c=0
while b  >= l:
    l*=3
    b*=2
    c+=1

print(c)


#pb Elep

n = int(input())
print((n+4)/5)
"""

###pb S and B
##k,n,w = map(int,input().split())
##b=0
####for i in range(1,w+1):
####    if n<k:
####        b+=(k-n)
####        n+=b-k
####    else:
####         n-=k
####    k*=i
######    print(k)
####print(b)
##t

###pb word
##
##n = input()
##u,l=0,0
##for i in n:
##    if i.isupper():
##        u+=1
##    elif i.islower():
##        l+=1
##if u>l:
##    print(n.upper())
##else:
##    print(n.lower())

###pb WS
##
##n,k=map(str,input().split())
##
##for i in range(int(k)):
##    if(n[-1] == '0'):
##        n=str(int(n)//10)
##    else:
##        n=str(int(n)-1)
##print(n)

n=input()

s=n.count('4') + n.count('7')

if s in [4,7]:
    print("YES")
else:
    print("NO")