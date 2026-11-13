# -*- coding: utf-8 -*-
"""
Created on Thu Jul 26 21:16:40 2018

@author: japes
"""

def check(k,z,n):
    if k==0:
        return 0
    
    counter=0
    for i in z:
        counter+=int(z[i]/k)
    
    if counter>=n:
         print(k)
     
    else:
        
        k=k-1
        check(k,z,n)
        
n,m  = map(int, input().split())
from collections import Counter
qlist=map(int,input().split())
z=Counter(qlist)
k=int(m/n)
check(k,z,n)