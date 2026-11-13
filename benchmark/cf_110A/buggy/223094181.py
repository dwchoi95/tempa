if __name__ == '__main__':
    num=input();
    
    cnt=0
    dumcnt=0
    new_num=str(num)
    
    for i in range(len(new_num)):
        if new_num[i] == '4' or new_num[i]=='7':
            cnt=cnt+1
            
            
    if(cnt==len(new_num)):
        print("YES")
    else:
        strcnt=str(cnt)
        for i in range(len(strcnt)):
            if strcnt[i]=='4' or strcnt[i]=='7':
                dumcnt=dumcnt+1
        
             
        if(dumcnt==len(strcnt)):
            print("Yes")
        else:
            print("NO")