original = input()

capitalized = original.capitalize()

swapedcase  = original.swapcase()

loweredcase = original.lower()



if swapedcase == capitalized or swapedcase == loweredcase:

    print(swapedcase)

else:

    print(original)