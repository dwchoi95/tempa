x=abs(int(input()))
k=1
cc=0
while x-k>=0:
    x-=k
    k+=1
    cc+=1
cc+=2*x
print(cc)