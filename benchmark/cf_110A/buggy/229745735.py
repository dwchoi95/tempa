Number=input("please enter the number :")
counter=0

for i in Number:
    if i =='4' or i =='7':
        counter+=1
if counter ==len(Number):
    print('YES')
else:
    print("NO")