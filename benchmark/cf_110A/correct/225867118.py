number = input()
number = number.strip()
number = [int(x) for x in list(number)]
lucky_count = 0
is_lucky = True

for num in number:
    if (num == 4) or (num == 7):
        lucky_count += 1

lucky_count_string = str(lucky_count)
lucky_count_list = [int(x) for x in list(lucky_count_string)]

for num in lucky_count_list:
    if (num != 4) and (num != 7):
        is_lucky = False
        break

if is_lucky:
    print("YES")
else:
    print("NO")