# -*- coding: utf-8 -*-
"""
Created on Tue Oct 10 11:35:12 2023

@author: 刘婉婷 2300012258
"""

def is_lucky(i):
    if i==0:
        return False
    while i>0:
        if i%10!=4 and i%10!=7:
            return False
        i=i//10
    return True

n=str(input())
a=n.count('4')+n.count('7')
if is_lucky(int(n)) or is_lucky(a):
    print('YES')
else:
    print('NO')