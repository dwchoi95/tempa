if __name__=="__main__":
    s=str(input())
    
    cnt=0
    
    for i in range(len(s)):
        if ord(s[i]) >= 65 and ord(s[i])<97:
            cnt=cnt+1
    
    if cnt == len(s):
        print(s.capitalize())
    elif cnt==(len(s)-1) and ord(s[0])>=97:
        print(s.capitalize())    
        
    else:
        print(s)
    print(cnt)
    print(ord(s[0]))