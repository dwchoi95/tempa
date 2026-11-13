n = list(input())
length = len(n)
i = 0
nearly_lucky = True
if length == 1 and '7' in n:
    print("NO")

else:
    while i < length:
        if n[i] == '4' or n[i] == '7':
            nearly_lucky = True

        else:
            nearly_lucky = False
            break
        i+=1

    if nearly_lucky == True:
        print("YES")
        
    else:
        print("NO")