# -*- coding: utf-8 -*-
"""
Created on Tue Sep 26 16:36:44 2023

@author: ghp
"""

number=input()
k=0
for i in range(len(number)):
    if number[i]=='4'or number[i]=='7':
        k=k+1
lucky=str(k)
result='YES'
for j in range(len(lucky)):
    if lucky[j]!='4' and lucky[j]!='7':
        result='NO'
print(result)