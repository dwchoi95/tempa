def lucky_number(n):
    c=0
    for i in n :
        if i=="4" or i=="7":
            c+=1
        else:
            return "No"
        
    if len(n)==c:
        return "Yes"
n=input()
res=lucky_number(n)
print(res)