n = input()
lucky_digits = ['4', '7']
lucky_counter = 0

for num in n:
    if num in lucky_digits:
        lucky_counter += 1

print("YES") if lucky_counter == 4 or lucky_counter == 7 else print("NO")