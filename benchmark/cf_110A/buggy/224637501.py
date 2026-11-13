def lucky_number(n):
    
    for i in n :
        if i != "4" or i!="7":
            return "NO"
        else:
            return "YES"
     
    
n=input()
res=lucky_number(n)
print(res)