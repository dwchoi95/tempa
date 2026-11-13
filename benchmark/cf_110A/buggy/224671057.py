n=int(input())
while(n):
    r=n%10
    n=n//10
    if(r!=4 and r!=7):
        print("no")
        exit()
        
print("yes")