from math import ceil
a = int(input())
a/=3
if a%1<0.5:
	a//=1
else:
	a=a//1+1
print(str(a//12)+' '+str(a%12))