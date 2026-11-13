n = input()

numoflucky = 0

for i in range(len(n)):
    if n[i] == "4" or n[i] == "7": numoflucky += 1

if numoflucky == 4 or numoflucky == 7: print("YES")
else: print("NO")