# -*- coding: utf-8 -*-
"""
Created on Tue Sep 12 15:24:27 2023

@author: 15110
"""
lst1=[]
lst2=[]
num=input()
for i in num:
    if i=='4':
        lst1.append(i)
    elif i=='7':
        lst2.append(i)
x=len(lst1)+len(lst2)
if x % 7 == 0 :
    print('YES')
else:
    print('NO')