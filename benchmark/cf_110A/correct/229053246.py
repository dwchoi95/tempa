def solve():
    
    n = int(input())
    ldc = 0
    while n > 0:
        ld = n % 10
        
        if ld == 4 or ld == 7:
            ldc += 1
        n //= 10
    
    if ldc == 4 or ldc == 7:
        print("YES")
    else:
        print("NO")
    
def main():
    T = 1
    while T > 0:
        solve()
        T -= 1
    
if __name__ == "__main__":
    main()