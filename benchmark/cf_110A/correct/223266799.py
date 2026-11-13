n = int(input())
num = n
count = 0
while num != 0:
    if num%10 == 4 or num%10 == 7:
        count+=1
    num//=10
if count == 4 or count == 7:
    print("YES")
else:
    print("NO")