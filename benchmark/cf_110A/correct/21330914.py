#!/bin/env python3
str = input()
s = str.count("4") + str.count("7")
if s == 4 or s == 7:
    print("YES")
else:
    print("NO")