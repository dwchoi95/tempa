st=str(input())
if st[0].islower() and st[1:].isupper():
    print(st.title())
elif st[0].isupper() and st[1:].islower():
    print(st)
if st[0].islower() and not st[1:].isupper():
    print(st)