def check(num):
    if len(num) == 1:
        return "NO"
    lucky = True
    for l in num:
        if l != '7' and l != '4':
            lucky = False
            break
        
    if(lucky):
        return("YES")
    else:
        return("NO")

num = input()
print(check(num))