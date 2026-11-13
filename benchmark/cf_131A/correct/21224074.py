w = input()
if w == w.upper():
    print(w.lower())
elif w[0] == w[0].lower() and w[1:] == w[1:].upper():
    print(w[0].upper()+w[1:].lower())
else: 
    print(w)