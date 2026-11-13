x = input()
total = ''
for i in range(len(x)):
    if int(x[i]) == 4 or int(x[i]) == 7:
        pass
    else:
        total = 'NO'
        break
print('YES' if total == '' else total)