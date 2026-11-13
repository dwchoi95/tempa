number = str( input("Enter number : "))

strike = 0
for i in range(len(number)) :
     if int(number[i]) == 4 or int(number[i])== 7 :
        strike +=1
    
if((strike==4 or strike==7)):
    print("Yes")
else:
    print("no")