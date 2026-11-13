n=int(input())
count=0
while n>0:
   t=n%10
   if t==4 or t==7:
       count+=1
   n=n//10
print(count)