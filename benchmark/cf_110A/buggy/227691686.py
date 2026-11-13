a = input()
counter4 = 0
counter7 = 0
skull = 0

for i in range(len(a)):
    if(a[i] == "4"):
        counter4 += 1
    elif(a[i] == "7"):
        counter7 += 1

if(skull == 0):
    if((counter4 + counter7 == len(a))and((counter4 != len(a))or(counter7 != len(a)))):
        print("YES")
    else:
        print("NO")
elif(skull != 0):
    if(counter4 == 4):
        print("YES")
    elif(counter7 == 7):
        print("YES")
    elif(counter4 == len(a)):
        print("NO")
    elif(counter7 == len(a)):
        print("NO")
    else:
        print("NO")