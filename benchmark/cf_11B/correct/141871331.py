x = abs(int(input()))
jumps = 0
pos = 0
while pos < x or (pos-x) % 2 != 0:
    jumps += 1
    pos += jumps
print(jumps)