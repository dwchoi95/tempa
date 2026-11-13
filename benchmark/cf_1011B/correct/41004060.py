nk=input().split(" ")
n=int(nk[0])
raw_food=input().split(" ")
food=[0]*101
for i in range(len(raw_food)):
    food[int(raw_food[i])]=food[int(raw_food[i])]+1
maxans=0    
i=1
people=0
while i<101:
    j=0
    gfood=food.copy()
    people=0
    while (j<101)and(people<n):
        if gfood[j]>=i:
            gfood[j]=gfood[j]-i
            people=people+1
        elif (gfood[j]<i):
            j=j+1
    if people==n:
        maxans=i
    i=i+1
print(maxans)