n = input()
if n.isupper() == True: print(n.swapcase())
elif n[0].isupper() == False and n[1:].isupper() == True: print(n.swapcase())
else: print(n)