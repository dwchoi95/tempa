cms=int(input())
from math import ceil 
inch=cms//36 
cms=cms%36 
print(inch,ceil(cms//3))