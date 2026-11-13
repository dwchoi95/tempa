n=input()
couter=0
for digit in n:
    if digit=="4" or digit=="7":
        counter=couter+1
a_counter=0
for digit in str(counter):
    if digit=='4' or digit=='7':
        a_counter=a_counter+1
if a_counter==len(str(counter)):
    output="Yes"
else:
    output="NO"
print(output)