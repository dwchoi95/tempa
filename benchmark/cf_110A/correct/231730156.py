n = int(input())
lucky = []
unlucky = []
for i in str(n):
    if i == "4" or i == "7":
        lucky.append(i)
    else:
        unlucky.append(i)
        
if len(lucky) == 4 or len(lucky) == 7:
    print("YES")
    
else:
    print("NO")