s=input()
s=s.lower()
s2=s[0]
s2=s2.upper()
for i in range(1,len(s),1):
    s2=s2+s[i]
print(s2)