lucky=list(map(int,input()))
res=1
for n in range(len(lucky)):
    if lucky[n] ==7 or lucky[n] == 4:
        continue
    else:
        print("NO")
        res=0
        break

if res == 1:
    print("YES")