n = input()
for i in range(len(n)):
    if n[i] != '4' or n[i] != '7':
        print('NO')
        break
    elif (n[i] == '4' or n[i] == 7) and i == len(n):
        print('YES')
        break