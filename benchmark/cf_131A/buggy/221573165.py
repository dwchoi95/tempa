s=input()
s2=''
s2+=s[0].upper()
n=len(s)
for i in range(1,n):
    s2+=s[i].lower()
print(s2)