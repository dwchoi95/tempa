import math as ma
from sys import exit
from decimal import Decimal as dec
def li():
	return list(map(int , input().split()))
# https://www.geeksforgeeks.org/multiplicative-inverse-under-modulo-m/
def modInverse(a , m):
	m0 = m
	y = 0
	x = 1
	if (m == 1):
		return 0
	while (a > 1):
		q = a // m
		t = m
		m = a % m
		a = t
		t = y
		y = x - q * y
		x = t
	if (x < 0):
		x = x + m0
	return x
def num():
	return map(int , input().split())
def nu():
	return int(input())
def find_gcd(x , y):
	while (y):
		x , y = y , x % y
	return x
n,m=num()
a=li()
f=[0]*101
for i in range(m):
	f[a[i]]+=1
l=0
r=101
ff=0
#print(f)
for j in range(1,101):
	pp=0
	#print("J",j)
	for i in range(101):
		pp+=f[i]//j
		#print("py",pp)
	if(pp>=n):
		ff=max(j,ff)
	#print(pp,ff,j)
print(ff)