#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Sep 12 23:29:59 2023

@author: huangxiaoyuan
"""

m=0
s=0
n=input()
if 1<=int(n)<=10**18:
    list=[]
    for i in n:
        list.append(i)
    list0=set(list)
    for i in list0:
        if i=='4':
            m+=list.count(i)
        if i=='7':
            s+=list.count(i)
        k=m+s
    if k==4 or k==7:
        print('YES')
    else:
        print('NO')