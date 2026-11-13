from collections import Counter

count = Counter(input())

if count['4'] + count['7'] in [4,7]:
    print('YES')
else:
    print('NO')