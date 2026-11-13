import math
x = abs(int(input()))
nr = 1
while(nr*(nr+1)/2 < x):
	nr += 1
while((nr*(nr+1)/2-x) % 2 == 1):
	nr += 1
print(nr)