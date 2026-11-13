def check(num):
    if len(num) == 1:
        return "NO"
    count = 0
    for l in num:
        if l == '7' or l == '4':
            count += 1
        
    if(count == 4 or count == 7):
        return("YES")
    else:
        return("NO")

num = input()
print(check(num))