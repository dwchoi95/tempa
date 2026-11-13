x=int(input())
t=0
p=1
while abs(x-t)>abs(x-t-p) :
    t+=p
    p+=1
print(p+abs(x-t)*2-1)