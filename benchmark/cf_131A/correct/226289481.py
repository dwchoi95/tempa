value = input()
if (value[0] == value[0].lower() and value[1:] == value[1:].upper()) or (value == value.upper()):
    print(value.swapcase())
else:
    print(value)