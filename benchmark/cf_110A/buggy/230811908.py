n = input()
lucky_nums = ['4', '7']

for num in n:
    if num not in lucky_nums:
        print("NO")
        exit()

print("YES")