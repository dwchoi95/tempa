a = input()
if len(a) == 1:
    if ord(a) >= 97:
        print(chr(ord(a) - 32))
    else:
        print(chr(ord(a) + 32))
else:
    check = 1
    for i in range(1 , len(a)):
        if ord(a[i]) < 65 or ord(a[i]) > 90:
            check = 0
            break
    if check == 1:
        for j in range(len(a)):
            if ord(a[j]) >= 97:
                print(chr(ord(a[j]) - 32) , end = "")
            else:
                print(chr(ord(a[j]) + 32) , end = "")
    if check == 0:
        print(a)