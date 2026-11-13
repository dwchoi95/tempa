soz = input()
res = ''
alphaBet = [ 'a','b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j','k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y' ,'z']
if soz[0] in alphaBet:
    res += soz[0].upper()+soz[1::].lower()
    print(res)
else:print(soz)