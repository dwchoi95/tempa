lucky=list(map(int,input()))

count=0
for n in range(len(lucky)):
    if lucky[n] ==7 or lucky[n] == 4 :

        count+=1


if count == 4 or count == 7:
    print("YES")
else:
    print("NO")