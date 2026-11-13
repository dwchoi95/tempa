a = float(input())
s = 0
i = 0
if a > 0:
    while a > s:
        i = i +1
        s = s + i
        if s >= a:
            print (int(s))
elif a ==0:
    print('1')
else:
    while a < s:
        i = i - 1
        s = s - i
        if s < a:
            print (int(s))