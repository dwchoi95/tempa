S = input()

count = 0
count1 = 0
for i in range(0,len(S)):
    if S[i].islower():
        count = count + 1
    elif S[i].isupper():
        count1 = count1 + 1
if count==1 or count1==1:
    print(S.title())
else:
    print(S)