st=input()
cnt=0
for i in st:
    if ord(i)<97:
        cnt+=1
if cnt==len(st) or ((cnt==len(st)-1) and ord(st[0])>=97):
    new_st=""
    for i in st:
        if ord(i)<97:
            new_st+=i.lower()
        else:
            new_st+=i.upper()
    print(new_st)
else:
    print(st)