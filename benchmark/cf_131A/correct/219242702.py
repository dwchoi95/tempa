import math



strToChange = input()

isNeedChange = True
newStr = strToChange
for idx in range(1, len(strToChange)):
    if strToChange[idx] != strToChange[idx].upper():
        isNeedChange = False
        break
if strToChange[0] == strToChange[0].upper() and isNeedChange:
    newStr = strToChange.lower()
    isNeedChange = False
if isNeedChange:
    newStr = strToChange[0].upper() + strToChange[1:len(strToChange)].lower()
print(newStr)