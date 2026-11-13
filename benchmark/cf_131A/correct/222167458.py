import math
#f = open("test.txt")

txt = input()

print([txt, txt.swapcase()][txt[1:].upper() == txt[1:]])