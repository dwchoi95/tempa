# -*- coding: utf-8 -*-
"""
Created on Sun Sep 17 10:01:18 2023

@author: lenovo
"""

name=list(input())
num=0
for i in range(len(name)):
    if name[i]==4 or name[i]==7:
        num=num+1
    else:
        continue
if num==4 or num==7:
    print("YES")
else:
    print("NO")