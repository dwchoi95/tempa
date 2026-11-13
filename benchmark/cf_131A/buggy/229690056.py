n=input()
arr=[]
for num in n:
    arr.append(num)
arr[0]=arr[0].upper()
for i in range(1,len(arr)):
    arr[i]=arr[i].lower()
brr=""
for b in arr :
    brr=brr+b
print(brr)