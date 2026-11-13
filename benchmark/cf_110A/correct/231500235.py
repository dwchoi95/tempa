a=input()
count=0
for i in a:
    if i=='4' or i=='7':
        count+=1
    
print("YES") if( count==4 or count==7) else print("NO")