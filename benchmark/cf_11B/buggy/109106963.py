"""
codeforces jumping jack 12B
"""


position = int(input())

ind = 0
positions = {0}

while True:
    if position in positions:
        break
    ind += 1
    pos = set()
    for i in positions:
        pos.add(i - ind)
        pos.add(i + ind)
    positions = positions | pos

print(ind)