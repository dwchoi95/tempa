string = input()
four = string.count("4")
seven = string.count("7")
a = str(four+seven)
f1 = a.count("4")
s1 = a.count("7")
if (len(a)==f1+s1):
    print("YES")
else:
    print("NO")