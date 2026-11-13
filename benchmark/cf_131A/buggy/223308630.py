S = input()

count = 0
ind = 0
count1 = 0
for i in range(0,len(S)):
    if S[i].islower():
        count = count + 1
        ind = i
if (count==1 and ind == 0):
    print(S.title())
else:
    print(S)