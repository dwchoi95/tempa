n = str(input())
if n.upper() == n:
    print(n[0]+n[1:-1].lower()+n[-1].lower())
elif n[0].lower() == n[0] and n[-1].upper() == n[-1] and n[1:-1].upper() == n[1:-1]:
    print(n[0].upper()+n[1:-1].lower()+n[-1].lower())
else: print(n)