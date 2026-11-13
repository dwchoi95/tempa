s = input()
counter = 0
for c in s:
    if c.isupper() == True:
        counter += 1
if counter == len(s) - 1 or counter == len(s):    
    print(s.capitalize())
else:
    print(s)