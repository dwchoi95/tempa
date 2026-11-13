t = input()
lst = list(t)
if len(t) == 1:
    if t.isupper():
        print(t.lower())
    else:
        print(t.upper())
    
elif len(t) > 1 and t.isupper():
    print(t.lower())

elif lst[0].islower() and ''.join(lst[1:]).isupper():
    lst[1:] = [char.lower() for char in lst[1:]]
    lst[0] = lst[0].upper()
    a = ''.join(lst)
    print(a)
    
else:
    print(t)