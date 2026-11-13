n=int(input())
numbers=list(str(n))
outputValues=" "
for i in numbers:
    if i=="4" or i=="7":
        outputValues="YES"
    else:
        outputValues="NO"
        break
print(outputValues)