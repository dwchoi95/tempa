a=input()
upper=0;lower=0
for i in a:
    if i.isupper(): upper+=1
    else:lower+=1
if upper>lower:print('Caps')
else:print('Lock')