def lucky_number(n):
    c=0
    for i in n:
        
        if (i=="4" or i=="7") and len(n)!= 1:
            c+=1
        else:
            return "NO"
    if len(n)==c :
         return "YES"
n=input()
print(lucky_number(n))