n = str(input())

count= 0
for i in range(len(n)):
    if (n[i] == '4') | (n[i] =='7'):
        count += 1
    
if (count == 4) | (count == 7) :
    print ("YES")
else :
    print ("NO")