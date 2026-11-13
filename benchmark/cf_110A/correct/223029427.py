input =input()
luckyLen = 0
for i in range(len(input)):
    if input[i] == '4' or input[i] =='7':
        luckyLen +=1
luckyLen = str(luckyLen)
lucky = True
for l in luckyLen:
    if l!= '4' and l!= '7':
        lucky = False 
if lucky:
    print("YES")
else:
    print("NO")