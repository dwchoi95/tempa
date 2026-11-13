def f():
    a=input()
    for i in range(1,len(a)):
        if not a[i].isupper():
             print(a)
             return
    print(a[0].upper()+a[1:].lower())
    # l=list(map(int,input().split()))
   
    
    
  
if __name__ == '__main__':
    # for _ in range(int(input())):
        f()