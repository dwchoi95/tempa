s=input()
count=0
nearly_lucky=False
for i in range(len(s)):
    if s[i]=='4' or s[i]=='7':
        count=count+1
        if count==4 or count==7:
            nearly_lucky=True

if nearly_lucky:
    print("YES")
else:
    print("NO")
        
#in 8 mins