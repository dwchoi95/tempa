values = input()



if (values[0].islower() and values[1:].isupper()):

    values = values.lower()

    print(values[0].upper() + values[1:])

elif values.isupper():

    print(values.lower())

elif (values[0].islower() and len(values) == 1):

    print(values.upper())

else:

    print(values)