#CodeForce Round 110a Nearly Lucky Number

number = input()
ln = number.count("4") + number.count("7")
sln = str(ln)
if all((c == "4" or c == "7") for c in sln):
    print("YES")
else:
    print("NO")