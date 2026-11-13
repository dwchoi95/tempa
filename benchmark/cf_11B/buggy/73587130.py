x = int(input())
jump = 0
cur_pos = 0
n_p = 0
while (True):
    if x == 0:
        break
    jump += 1
    n_p = cur_pos + jump
    if n_p <= x:
        cur_pos += jump
    if n_p > x:
        cur_pos -= jump
    if cur_pos == x:
        break

print(jump)