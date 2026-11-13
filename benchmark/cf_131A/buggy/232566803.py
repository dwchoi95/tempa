n = str(input())
if n.isupper() :print(n.lower()) 
elif n[1:].isupper() :print(n[0].capitalize()+n[1:].lower())        
else :print(n)