a=str(input())
s=0
output=str()
for i in range(1, len(a)):
    if a[i].isupper():
        s+=1
if s==len(a) or s+1==len(a):
    output+=str(a[0]).upper()
    for j in range(1, len(a)):
        output+=(str(a[j]).lower())
    print(output)
else:
    print(a)