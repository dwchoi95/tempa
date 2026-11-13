inp = input()

if inp.isupper():
    print(inp.lower().capitalize())
else:
    if inp[0].islower() and inp[1:].isupper():
        print(inp.lower().capitalize())
    else:
        print(inp)