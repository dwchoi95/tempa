s = list(map(int, input()))
lucky = {4:0, 7:0}
for i in s:
    if i in lucky:
        lucky[i] += 1
if sum(lucky.values()) == 4:
    print('YES')
elif sum(lucky.values()) == 7:
    print('YES')
else:
    print('NO')