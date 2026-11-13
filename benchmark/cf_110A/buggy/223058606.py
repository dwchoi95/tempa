# -*- coding: utf-8 -*-
"""
Created on Tue Sep 12 16:30:18 2023

@author: gzk16
"""

lucky_number = input()
numbers = [int(x) for x in lucky_number]
if all(x == 4 or x == 7 for x in numbers):
    print('YES')
else:
    count = 0
    for number in numbers:
        if number == 4 or number == 7:
            count += 1
    if count == 4 or 7:
        print('YES')
    else:
        print('NO')