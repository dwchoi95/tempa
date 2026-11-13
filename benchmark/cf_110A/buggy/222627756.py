# O(n)
n = input()
r = ""
for i in range (len(n)):
    if (n[i] == '7' or n[i] == '4'):
        r = "YES"
    else: 
        r = "NO"
        break
        
print (r)