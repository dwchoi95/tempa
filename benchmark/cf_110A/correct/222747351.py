def is_lucky(digit):
    return digit=='4' or digit=='7'
def count_lucky(n):
    ct=0
    for i in str(n):
        if is_lucky(i):
            ct+=1
    return ct
n=int(input())
res=count_lucky(n)
if is_lucky(str(res)):
    print("YES")
else:
    print("NO")