s_num = input()


def is_lucky(s_num):
    return not bool(s_num.replace('7', '').replace('4', ''))


print('YES' if is_lucky(s_num) else 'NO')