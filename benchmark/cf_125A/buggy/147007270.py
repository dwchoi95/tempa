def fi(n):
    # n in cm
    
    ft = n//36
    rem = n % 36
    ic = round(rem/3)
    
    return ft,ic
    
    return 
        
#main program

n = int(input())
a,b = fi(n)
print(a,b)