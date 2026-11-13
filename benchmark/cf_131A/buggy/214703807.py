#https://codeforces.com/problemset/problem/131/A
s=str(input())
''''''
s1=[]
for i in range(1,len(s)):
    s1.append(s[i])
s2=''.join(s1).split()
#print(s2[0].isupper())
if s2[0].isupper()==True:
    a=s.capitalize()
    print(a)
else:
    print(s)