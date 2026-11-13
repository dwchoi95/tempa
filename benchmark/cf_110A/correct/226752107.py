n=int(input())
numbers=list(str(n))
luckyNumbers=0
outputValues=" "
for i in numbers:
    if i=="4":
        luckyNumbers +=1
    elif i=="7":
        luckyNumbers +=1
if luckyNumbers==4 or luckyNumbers == 7:
    outputValues="YES"
else:
    outputValues="NO"
print(outputValues)