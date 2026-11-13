num = int (input())


lucky = True
while num > 0 :
    if (num % 10) == 4 or (num % 10) ==7 :
        lucky = True
        num //= 10
    else :
        lucky = False
        break

if lucky == True :
    print("YES")
else:
    print("NO")