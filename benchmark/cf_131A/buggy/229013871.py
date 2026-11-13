p = input()


if(p == p.upper() or p[1:len(p)]==p[1:len(p)].upper()):
    l = []
    nl = list(p.lower())
    l.append(nl[0].upper())
    l.extend(nl[1:len(p)])
    print(''.join(l))
else:
    print(p)