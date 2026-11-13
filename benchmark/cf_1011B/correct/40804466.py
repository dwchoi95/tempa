#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Jul 26 21:12:19 2018

@author: manish
"""

n, k = input().split()
s = input().split()
n, k = int(n), int(k)

'''
n, k = 3,9
s=  '42 42 42 42 42 42 42 42 42'.split()
'''
d = sorted(s)

ref = d[0]


if k > 1 and n<=k:
    counts = []
    count = 1
    for i in range(1, len(d)):
        
        if d[i] == ref:
            count+=1
            
        else:
            counts.append((d[i-1], count))
            
            count =1
            ref = d[i]
    counts.append((d[i], count))
    for i in range(k,0, -1):

        add = 0
        for j in range(0, len(counts)):
            add += counts[j][1]//i

        if add >= n:
            ans = i
            break
elif k == 1 and n==1:
    ans = 1

else:
    
    ans = 0
    

print(ans)