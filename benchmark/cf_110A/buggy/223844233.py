my_str=input()

a=my_str.count('4')
b=my_str.count('7')

if a=='4' or a=='7' or b=='4' or b=='7' or a+b=='4' or a+b=='7':
    print("Yes")
    
else:
    print("No")