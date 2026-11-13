n=input()
count=0
for i in range(0, len(n)):
    if n[i] == "4" or n[i]=="7":
        count+=1
count=str(count)
ans=True
for i in range(0, len(count)):
    if count[i] == "4" or count[i]=="7":
        ans=True
    else:
        ans=False
        break
if ans==False:
    print("NO")
else:
    print("YES")