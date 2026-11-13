# -*- coding: utf-8 -*-
"""
Created on Sat Sep 16 22:36:35 2023

@author: He'Bing'Ru
"""

num = list(input())
out = 0
for i in num :
    if (i == '4') + (i == '7') :
        out += 1
if (out%4 == 0) + (out%7 == 0) + (out%47 == 0) + (out%74 == 0) :
    print('YES')
else:
    print('NO')