pos = 0
i = 1

x = int(input())

while pos+i<=x:
    if pos + i > x:
        pos -= i
    else:
        pos += i
    i += 1
print(i+1)