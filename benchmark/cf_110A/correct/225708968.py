a=input()
l=list(a)
s=0
for i in l:
    b=int(i)
    if b in [4,7]:
        s+=1
l1=list(str(s))
mess='YES'
for i in l1:
    if int(i) != 4 and int(i)!=7:
        mess='NO'
print(mess)