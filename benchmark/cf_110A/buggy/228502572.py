def lucky(value):
    value = str(value)
    return not bool(value.replace('4', '').replace('7', '4'))


def so_close_lucky(value):
    value = str(value)
    without_lucky = value.replace('4', '').replace('7', '')
    if lucky(len(value) - len(without_lucky)):
        return True
    else:
        return False


num = input()
print('YES' if so_close_lucky(num) else 'NO')