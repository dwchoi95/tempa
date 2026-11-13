x = int(input())
count = 0
pos = 0
pos1 =0
while pos!=x:
    count+=1
    pos1 = pos + count
    if pos1<x:
        pos = pos +count
    elif pos1>x:
        pos = pos - count
    elif pos1 == x:
        pos = pos + count
print(count)