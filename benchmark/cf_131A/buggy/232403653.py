y= input()
if y.isupper() or (y[0].islower()) and (y[1:].isupper) or (len(y)==1) and (y.lower):
   y=y.swapcase()

print(y)