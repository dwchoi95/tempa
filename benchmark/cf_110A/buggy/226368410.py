lucky_nums = input()
lucky_nums_str = str(lucky_nums)
lucky_nums_split = list(lucky_nums_str)
ans=0
for digit in lucky_nums_split:
    if digit == '4' or digit == '7':
        ans='YES'
    else:
        ans='NO'
print(ans)