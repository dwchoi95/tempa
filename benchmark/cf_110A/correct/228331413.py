#СЛИШКОМ ДЛИННЫЕ СЛОВА
'''
n = int(input())
for i in range(n):
	s = input()
	s1 =" "
	if(len(s)>10):
		s1 = s[0]
		s1 += str(len(s)-2)
		s1 += s[-1]
	else:
		s1 = s
	print(s1)
'''
#КОМАНДА
'''
#include <iostream>
 
using namespace std;
 
int main()
{
  int a,b,f,c,d,count=0;
  cin>>d;
  for(int i;i<d;i++){
      cin>>a>>b>>c;
      if (a+b+c==3 || a+b+c==2){
          count++;
      f=count;
    
  }
 
}
cout<<f;
}
'''
#СЛЕДУЙЩИЙ РАУНД
'''
a,b = map(int,input().split())
count = 0
l = list(map(int,input().split()))
for i in range(a):
    if l[i] >= l[b-1] and l[i] > 0:
        count += 1
print(count)
'''
#Bit++
'''
a=int(input())
count=0
for i in range(a):
    y=input()
    if (y=="X++" or y=="++X"):
        count+=1
    if (y=="X--" or y=="--X"):
        count-=1
print(count)
'''
#МАТЕМАТИКА СПЕШИТ НА ПОМОЩ
'''
a=list(input())
a.sort()
while ("+"in a):
    a.remove("+")
s=("+").join(a)
print(s)
'''
#КАПИТАЛИЗАЦИЯ СЛОВА
'''
a=list(input())
a[0]=a[0].upper()
b=("").join(a)
print(b)
'''
#ДЕВУШКА ИЛИ ЮНОША
'''
a=list(input())
count=0
l=[]
for i in range(len(a)):
    if a[i] not in l:
        l.append(a[i])
        count+=1
if (count%2==0):
    print("CHAT WITH HER!")
if (count%2!=0):
    print("IGNORE HIM!")
'''
#КАМНИ НА СТОЛЕ
'''
d=int(input())
s=list(input())
count=0
for i in range (1,d):
    if(s[i-1]==s[i]):
        count+=1
print(count)
'''
#упражнение на строки
'''
a=["A","O","Y","E","U","I","a","o","y","e","u","i"]
n=list(input())

'''
#МИШКА И СТАРШИЙ БРАТ
'''
a,b = map(int,input().split())
count=0
while a<=b:
    a*=3
    b*=2
    count+=1
print(count)
'''
#СЛОНИК
'''
d=int(input())
if (d%5==0):
    print(d//5)
if (d%5!=0):
    print(d//5+1)
'''
#СОЛДАТ И БАНАНЫ
'''
a,b,c= map(int,input().split())
count=1
ff=0
for i in range(c):
    d=a*count
    ff+=d
    count+=1
if(ff<b):
    print(0)
if(ff>=b):
    print(ff-b)
'''
#СЛОВО
'''
a=["A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z"]
b=["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"]
g=list(input())
count1=0
count2=0
for i in range(len(a)):
    if (a[i]in g):
        count1+=1
    if (b[i]in g):
        count2+=1
dd=("").join(g)
if(count2>=count1):
    ss=dd.lower()
    print(ss)
if (count2<count1):
    hh=dd.upper()
    print(hh)
print(count1)
print(count2)
'''
#ЮНЫЙ ФИЗИК
'''
s=int(input())
l=[]
g=0
for i in range (s):
    for i in range(1):
        c,b,a = map(int, input().split())
        f=c+b+a
        l.append(f)
for i in range (len(l)):
    g+=l[i]
if (g==0 and c+b+a!=-3):
    print("YES")
if (g!=0 or c==-3 and b==0 and a==0 ):
    print("NO")

'''
#НЕПРАВИЛЬНОЕ ВЫЧИТАНИЕ
'''
a,b= map(int,input().split())
for i in range(b):
    if(a%10!=0):
        a=a-1
    else:
        a = a // 10
print(a)
'''
#ФУТБОЛ
'''
f=list(input())
d=["0"]
h=["1"]
count=0
c=0
for i in range(len(f)):
    if (d[0]in f):
        count+=1
    if(h[0]in f):
        c+=1
if(c>=7 or count>=7):
    print("YES")
else:
    print("NO")
print(c)
print(count)
'''
#Счастливое число

f=list(input())
count=0
while ("4"in f):
    s=f.remove("4")
    count+=1
while ("7"in f):
    d=f.remove("7")
    count+=1
if (count==4 or count==7):
    print("YES")
else:
    print("NO")