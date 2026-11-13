ring=input()
res=list(ring)
val=len(ring)
for i in range(val):
    if i==0 and ord(res[i])>96:
        char=ord(res[i])
        res.pop(i)
        res.insert(i,chr(char-32))
    elif i!=0 and ord(res[i])<96:
        char=ord(res[i])
        res.pop(i)
        res.insert(i,chr(char+32))
print("".join(res))