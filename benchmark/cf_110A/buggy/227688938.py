n=input()
count=0
for i in range(0, len(n)):
    if n[i] == "4" or n[i]=="7":
        count+=1
count=str(count)
count2=0
ans=None
for i in range(0, len(count)):
    if count[i] == "4" or count[i]=="7":
        count2+=1
if count2==int(count):
    print("YES")
else:
    print("NO")