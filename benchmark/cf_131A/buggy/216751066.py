inpStr = input()

capsNum = 0

for char in inpStr:
    if char.isupper():
        capsNum += 1
if capsNum == len(inpStr):
    print(inpStr.lower())
elif capsNum == len(inpStr) - 1:
    print(inpStr[0].upper() + inpStr[1:].lower())
else:
    print(inpStr)