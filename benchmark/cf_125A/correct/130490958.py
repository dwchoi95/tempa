centimeters = int(input())
mod = centimeters % 36
if mod == 35:
    div = int(centimeters/36) + 1
    print(div, 0)
else:
    div = int(centimeters/36)
    newMod = mod % 3
    newDiv = int(mod/3)
    if newMod == 2:
        newDiv += 1
    else:
        pass
    print(div, newDiv)