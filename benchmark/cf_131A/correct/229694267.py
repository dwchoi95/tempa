n=input()
flag=True
arr=[]
for num in n:
    arr.append(num)
for i in range(1,len(arr)):
    if arr[i].islower():
        flag=False
if flag==True:
    if arr[0].isupper():
        for i in range(0,len(arr)):
            arr[i]=arr[i].lower()
    else:
        arr[0]=arr[0].upper()
        for i in range (1,len(arr)):
            arr[i]=arr[i].lower()
brr=""
for b in arr :
    brr=brr+b
print(brr)