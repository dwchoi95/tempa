x=int(input())
t=0
p=1
if x>=0:
    while abs(x-t)>abs(x-t-p) :
        t+=p
        p+=1
    print(p+abs(x-t)*2-1)
else:
    x=-x
    while abs(x-t)>abs(x-t-p) :
        t+=p
        p+=1
    print(p+abs(x-t)*2-1)