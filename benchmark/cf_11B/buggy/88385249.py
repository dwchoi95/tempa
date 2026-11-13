#rOkY
#FuCk

################################## kOpAl #######################################

t=int(input())
if(t<0):
    t=-t

r=0
f=0

while(f<t or (r-t)%2!=0):
    r+=1
    f+=r
print(r+1)