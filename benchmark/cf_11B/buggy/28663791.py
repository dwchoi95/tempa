n=int(input())
s=1
p=0
while p<n:
    if s+s+1 >n-p and n-p!=s:
        s+=1
    else:
        p+=s
        s+=1
print(s-1)