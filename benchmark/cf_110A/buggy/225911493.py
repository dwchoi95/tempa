import collections
num = int(input())
snum = str(num)
obj = collections.Counter(snum)

if(obj['4'] in [4,7] or obj['7'] in [4,7]):
    print("YES")
else:
    flag = 1
    while num:
        if(num%10 in [4,7]):
            num//=10
            continue
        else:
            flag = 0
            print("NO")
            break
    if(flag):
        print("YES")