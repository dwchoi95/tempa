s = input()
counter = 0
for c in range(1, len(s)):
    if s[c].isupper() == True:
        counter += 1
if counter == len(s) - 1:    
    print(s.capitalize())
else:
    print(s)