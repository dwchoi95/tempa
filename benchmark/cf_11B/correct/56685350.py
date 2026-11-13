"""
Jack is working on his jumping skills recently. Currently he's located at point zero of the number line. He would like to get to the point x. In order to train, he has decided that he'll first jump by only one unit, and each subsequent jump will be exactly one longer than the previous one. He can go either left or right with each jump. He wonders how many jumps he needs to reach x.

Input
The input data consists of only one integer x ( - 109 ≤ x ≤ 109).

Output
Output the minimal number of jumps that Jack requires to reach x.
"""
from math import *

def is_even(a):
    return False if a%2 else True

def calc_sum(n):
    return n * (n + 1)/2

def check(a, x):
    return (not is_even(a) and not is_even(x)) or (is_even(a) and is_even(x))

x = abs(int(input()))

if x == 0:
    print(0)
else:
    n = (-1+pow(1+4*2*x, 0.5))/2

    ceil_n = ceil(n)

    if check(calc_sum(ceil_n), x):
        print(ceil_n)
    else:
        if check(calc_sum(ceil_n + 1), x):
            print(ceil_n + 1)
        else:
            print(ceil_n + 2)