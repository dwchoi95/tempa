# -*- coding: utf-8 -*-
"""
Created on Mon Oct  9 14:22:36 2023

@author: 25419
"""

word=input()
str1='QWERTYUIOPASDFGHJKLZXCVBNM'
for i in range(1,len(word)):
    if word[i] not in str1:
        print(word)
        break
    elif word[i] in str1 and i!=len(word)-1:
        pass
    else:print(word.swapcase())