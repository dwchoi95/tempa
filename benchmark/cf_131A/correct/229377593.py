a = list(input())
 
 
def byk1(a):
    
    for i in a[1:]:
        if i.istitle() == False:
            r = ''.join(a)
            return r
        
    g = []
    for i in a:
        if i.istitle() == False:
            b = i.upper()
            g.append(b)
        elif i.istitle() == True:
            b = i.lower()
            g.append(b)
    r = ''.join(g)
    
    return r
 
 
print(byk1(a))