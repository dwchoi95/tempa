n = str(len([x for x in input() if x == "4" or x == "7"]))

r = "YES"

for x in n:

    if x == "4" or x == "7":

        continue

    else:

        r = "NO"

        break



print(r)