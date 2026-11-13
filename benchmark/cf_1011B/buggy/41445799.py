amount = list(map(int, input().split(' ')[:2]))
complects = list(map(int, input().split(' ')[:amount[1]]))
complects.sort()
comp = list()
for i in range(len(complects)):
    if i == 0:
        comp.append(1)
    elif complects[i] != complects[i - 1]:
        comp.append(1)
    else:
        comp[len(comp) - 1] += 1
comp.sort()
#print(comp)
compPair = list()
for i in range(amount[0]):
    if i < len(comp):
        compPair.append([comp[i], i])
    else:
        compPair.append([0, i])
compPair.sort()
success = False
#print(compPair, "compPair")
while True:
    success = False
    before = compPair[0][0]
    #print(compPair)
    for i in range(len(compPair) - 1, 0, -1):
        if compPair[i][1] == compPair[0][1] and compPair[i][0] - 1 >= compPair[0][0] + 1:
            compPair[i][0] -= 1
            compPair[0][0] += 1
            success = True
            break
    if success == False:
        for i in range(len(compPair) - 1, 0, -1):
            if compPair[i][0] - compPair[0][0] - 1 > compPair[0][0]:
                #print(compPair[i][0])
                for j in range(len(compPair) - 1, 0, -1):
                    if compPair[i][1] == compPair[0][1]:
                        compPair[i][0] += compPair[0][0]
                        break
                compPair[i][0] -= compPair[0][0] + 1
                compPair[0][0] += 1
                compPair[0][1] = compPair[i][1]
        #print(compPair)
    if before == compPair[0][0]:
        break
    compPair.sort()
print(compPair[0][0])