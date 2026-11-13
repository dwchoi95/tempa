def lucky(n):
    num = str(n)
    a = 0
    for i in range(len(num)):
        if num[i] == "4" or num[i] == "7":
            a = a + 1 
    # print(a)
    if a == 4 or a == 7:
        return True
    else:
        return False
n = int(input())
check = lucky(n)
if check == True:
    print("YES")
else:
    print("NO")