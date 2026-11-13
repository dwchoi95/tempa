l= input()
if l.isupper() or (l[0].islower()) and (l[1:].isupper) or (len(l)==1) and (l.lower):
   l=l.swapcase()

print(l)