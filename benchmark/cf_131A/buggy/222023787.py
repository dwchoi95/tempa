x = list(input())
flag1 = True
flag2 = True
flag3 = True
flag4 = False
string = ''
for i in range(len(x)):
    if x[i] != x[i].capitalize():
        flag1 = False
    if flag1:
        while i >= 1:
            x[i] = x[i].lower()
            i = i - 1
        string = ''.join([i for i in x])
        flag4 = True
        print(string)
if x[0] != x[0].capitalize():
    flag2 = True
for i in range(1, len(x)):
    if x[i] == x[i].lower():
        flag3 = False

i = len(x) - 1
if not flag4:
    if flag2 == True and flag3 == True:
        x[0] = x[0].capitalize()
        while i >= 1:
            x[i] = x[i].lower()
            i = i - 1
        string = ''.join([i for i in x])
        print(string)
    else:
        string = ''.join([i for i in x])
        print(string)