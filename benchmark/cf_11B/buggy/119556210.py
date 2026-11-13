def main():
    x = int(input())
    num = ans = 0
    
    
    while num != x:
        if num+ans+1 <= x: 
            ans += 1
            num += ans
        
        elif num+ans+1 > x: 
            ans += 1
            num -= ans
        
    print(ans)

if __name__ == "__main__":
    main()