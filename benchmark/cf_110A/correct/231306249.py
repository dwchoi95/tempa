def lucky(n):
    c=0
    while n>0:
        r=n%10
        if r==4 or r==7:
            c+=1
        n//=10
    return c in [4,7]
if __name__=="__main__":
    n=int(input())
    if lucky(n):
        print("YES")
    else:
        print("NO")