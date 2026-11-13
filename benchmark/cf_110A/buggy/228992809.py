n = int(input())
n = str(n)
if "4" or "7" in n:
    count = 0
    for digit in n:
        if digit == '4' or digit == '7':
            count +=1
    if count == len(n):
        print('YES')
    else:
        count = str(count)
        c = 0
        for d in count:
            if d =='4' or d == '7':
                c += 1
        if c == len(count):
            print('YES')  
else:
    print('NO')