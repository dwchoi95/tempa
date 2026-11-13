input_string = input()
needs_change = True
for i in range(1, len(input_string)):
    if input_string[i].islower():
        needs_change = False
        break
if needs_change:
    input_string = input_string.swapcase()
print(input_string)