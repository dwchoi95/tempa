#!/bin/env python3
str = input()
flag = 0
for i in range(len(str)):
    if ord(str[i]) - ord("a") >= 0:
        flag = 1
        break
if flag == 0:
    print(str.lower())
    exit()

for i in range(len(str)-1):
    if ord(str[i+1]) - ord("a") >= 0:
        flag = 0
        break
if flag == 0:
    print(str)
else:
    print(str[0].upper() + str[1:].lower())