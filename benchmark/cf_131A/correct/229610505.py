st=input()
count=0
for i in st:
    if i.islower():
        count+=1
if count<=1 and st[0].islower():
    print(st.title())
elif st.isupper():
    print(st.lower())
else:
    print(st)