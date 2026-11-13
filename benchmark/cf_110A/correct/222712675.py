a = int(input())

count = 0

while True:
    last = a%10
    if last == 4 or last ==7:
        count+=1
    a = a//10
    if a==0:
        break

if count%10 == 4 or count%10 ==7:
    print("YES")
else:
    print("NO")