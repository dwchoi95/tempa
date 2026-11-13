def xingyun(n):
    n = str(n)
    if n == "7" or n == "4":
        return True
    for l in range(len(n)):
        if n[l] != "7" or n[l] != "4":
            return False
        else:
            continue
    return True
    
    
N = str(input())
su = 0
for i in range(len(N)):
    if N[i] == "7" or N[i] == "4":
        su += 1
if xingyun(su):
    print("Yes")
else:
    print("No")