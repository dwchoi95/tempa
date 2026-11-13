num = abs(int(input()))
if num < 2:
    print(num)
else:    
    n = 0
    t = 0    
    diff = None
    while True:
        n += 1
        tn = t + n
        if tn < num:
            t = tn
        elif tn == num:    
            print(n)
            break
        else:
            if tn % 2 != num % 2:
                t  = tn
            else:
                if diff is None:
                    t = tn
                    diff = t - num
                if diff < 2 * n:
                    print(n)
                    break