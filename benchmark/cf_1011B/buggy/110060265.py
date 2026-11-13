arr=input().split()
n=int(arr[0])
m=int(arr[1])
arr=list(map(int,input().split()))
if m<n:
    print(0)
elif len(arr)==len(set(arr)):
    print(1)
else:
    lst=[]
    for i in list(set(arr)):
        lst.append(arr.count(i))
    print(sum(lst[0:n-1])//n)