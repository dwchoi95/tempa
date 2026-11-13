n=input()
count=0
for i in range(len(n)):
    if int(n[i])==4 or int(n[i])==7:
        count+=1
a='YES'
b=str(count)
for j in range(len(b)):
    if int(b[j])!=4 or int(b[j])!=7:
        a='NO'
        break
print(a)