s = input() 
n = len(s) 
dem = 0
ok = 0  
if 'A' <= s[0] <= 'Z':
    ok = 1 
for x in s :
    if'A' <= x <= 'Z' : 
        dem += 1 
if dem == n or (dem == n - 1 and ok == 0):
    s = s.capitalize() ; 
print(s) ;