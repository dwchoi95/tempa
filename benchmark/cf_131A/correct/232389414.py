i = input()
if i.isupper() or (i[0].islower()) and (i[1:].isupper()) or (len(i)==1 and  i.islower()):
    i = i.swapcase()
print(i)