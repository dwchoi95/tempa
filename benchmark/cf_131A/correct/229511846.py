s = input()

check =0
new_s=""
if (s[0]>='a' and s[0]<='z') or (s[0] >="A" and s[0] <="Z"):
    for i in range(1,len(s)):
        if s[i] >='a' and s[i]<='z':
            check = 1
            break
    
        else:
            continue
            

if check == 0:
    for i in range(len(s)):
        if s[i] >='a' and s[i] <= 'z':
            new_s+=chr(ord(s[i])-32)
        else:
            new_s+=chr(ord(s[i])+32)

    print(new_s)

else:
    print(s)