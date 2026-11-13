n = int(input())
lucky = 0
for i in str(n):
    if i == '4':
        lucky += 1
    if i == '7':
        lucky += 1

# print(lucky)
if lucky == 4 or lucky == 7:
    print('YES')
else:
    print("NO")