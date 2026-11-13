input =int(input())
luckyLen = 0
while input!=0:
    if input%10==4 or input %10 ==7:
        luckyLen += 1
    input  = int(input/10)
while luckyLen!=0:
    if luckyLen%10!=4 and luckyLen %10 !=7:
        print("NO")
        exit()
    luckyLen  = int(luckyLen/10)
print("YES")