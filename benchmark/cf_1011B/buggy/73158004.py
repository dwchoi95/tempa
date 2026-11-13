from math import floor
n,m=map(int, input().split());
d={};
s=input().split();
for i in s:
    try:
        d[i]+=1;
    except:
        d[i]=1;

maximum=floor(m/n);
print(maximum)