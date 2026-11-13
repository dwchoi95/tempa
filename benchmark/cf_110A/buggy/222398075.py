num=(list(input()))
n=set(num)
if("4" in n and "7" in n):
    a,b=num.count("4"),num.count("7")
    if(a+b==4 or a+b==7):
        print("YES")
    else:
        print("NO")
else:
    print("NO")