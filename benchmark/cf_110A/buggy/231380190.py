def lucky():
    n=input()

    for i in range(len(n)):
        if n[i] not in ('4','7'):
            return 'NO'
    return 'YES'

print(lucky())