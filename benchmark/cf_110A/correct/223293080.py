# -*- coding: utf-8 -*-
"""
Created on Thu Sep 14 11:07:49 2023

@author: ljy
"""

n=input()
luc=0
for i in range(len(n)):
    if n[i]=='4' or n[i]=='7':
        luc+=1
#print(luc)
if luc==4 or luc==7:
    print('YES')
else:print('NO')