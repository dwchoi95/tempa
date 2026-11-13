# -*- coding: utf-8 -*-
"""
Created on Thu Sep  7 15:21:48 2023

@author: mac
"""

s = input()
if s.isupper():
    print(s.lower())
elif s[1:].isupper():
    print(s[0].upper() + s[1:].lower())
else:
    print(s)