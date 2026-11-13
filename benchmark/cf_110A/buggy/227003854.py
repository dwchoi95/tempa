def lucky(a):
    list = ['4','7']
    count = 0
    for i in range(len(a)):
        if a[i] in list:
            count += 1
    if count == len(a):
        return'YES'
    else:
        return'NO'
b = input()
c = lucky(b)
print(c)