#!/usr/bin/env python3

import sys
import string

word = sys.stdin.readline().strip()

for letter in word[1:]:
    if letter not in string.ascii_uppercase:
        print(word)
        exit()

print(word[0].lower() if word[0].isupper() else word[0].upper(), word[1:].lower(), sep='')