n=int(input())
s=0;m=0
while 1:
    if m==n:
        print(s)
        break
    if m>n:
        print(s+1)
        break
    s+=1
    m+=s