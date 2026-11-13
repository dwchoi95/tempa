# -*- coding: utf-8 -*-
"""
Created on Tue Oct 10 11:35:12 2023

@author: 刘婉婷 2300012258
"""

def is_lucky(n):
    while n>0:
        if n%10!=4 or n%10!=7:
            return False
        n=n//10
    return True

n=str(input())
if is_lucky(n.count('4')+n.count('7')):
    print('YES')
else:
    print('NO')