def lucky(a):
    a = str(a)
    list = ['4','7']
    count = 0
    for i in range(len(a)):
        if a[i] in list:
            count += 1
    if count == len(a):
        return'YES'
    else:
        return'NO'
def nearly_lucky(b):
    b = str(b)
    num = b.count('4') + b.count('7')
    if lucky(num):
        return'YES'
    else:
        return'NO'
c = input()
d = nearly_lucky(c)
print(d)