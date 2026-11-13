x = int(input())
count = 0
pos = 0
pos1 =0
while pos!=x and x!=0:
    count+=1
    if x>0:
        pos1 = pos + count
    elif x<0:
        pos1 = pos - count
    if pos1<x:
            pos = pos + count
    elif pos1>x:
        pos = pos - count
    elif pos1 == x and x>0:
        pos = pos + count
    elif pos1 == x and x<0:
        pos = pos - count
print(count)