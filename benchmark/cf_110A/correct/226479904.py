m=input()
k=m.count("4")+m.count('7')
for i in str(k) :
    if i!="4" and i!="7":
        m="NO"
        break
if m!="NO":
    m='YES'
print(m)