a = input().split('+')
a.sort()
b = ''

for i in a:
    b = b + i + '+'
print(b[0:-1])