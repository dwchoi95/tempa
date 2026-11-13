n=int(input())
def fun(n):
    r=0
    while(n!=0):
        r=n%10
        if r!=4 and r!=7:
            return "No"
        n=n/10
    return "YES"
print(fun(n))