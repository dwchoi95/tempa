def lucky():
    n=input()
    if n.count('4') + n.count('7') in (4,7):
        return 'YES'
    else:
        return 'NO'

print(lucky())