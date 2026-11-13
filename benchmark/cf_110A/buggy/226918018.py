x = list(map(int, input()))
print('YES' if all(i == 7 or i == 4 for i in x) else 'NO')