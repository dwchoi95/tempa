s = input()
capital= ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z']
# capital = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']
c = 0
all = 0
l=0
for i in range(0,len(s)):
    if (s[i] in capital):
        c+=1
    all+=1
if (all == c):
    print(s.lower()) 
elif (s[0]==s[0].lower()):
    for i in range(1,len(s)):
        if(s[i]==s[1]):
            l+=1
    if(l>0):
        print(s)
    else:
        print(s[0].upper(),end="")
        for i in range(1,len(s)):
            print(s[i].lower(),end="")
else:
    print(s)