n=int(input())
st=str(n)
fors=st.count("4")
sevens=st.count("7")
sum=fors+sevens
if sum==4 or sum==7:
    print("YES")
else:
    print("NO")