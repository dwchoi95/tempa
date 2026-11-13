input =int(input())
luckyLen = 0
while input>0:
    if input%10==4 or input %10 ==7:
        luckyLen += 1
    input  = int(input/10)
if luckyLen==4 or luckyLen==7:
    print("YES")
else:
    print("NO")