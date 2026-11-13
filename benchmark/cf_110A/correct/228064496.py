n = input()
count = 0
for i in n:
    if i == '4' or i == '7':
        count += 1
ris = 'YES'
for i in str(count):
    if i != '4' and i != '7':
        ris = 'NO'
print(ris)