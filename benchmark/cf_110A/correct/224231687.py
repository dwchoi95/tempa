if __name__ == '__main__':
    n = input()
    num_ld = 0
    count = 0
    for digit in n:
        if digit == '4' or digit == '7':
            num_ld = num_ld + 1
    for digit in str(num_ld):
        if digit not in ['4', '7']:
            print('NO')
            break
        elif digit == '4' or digit == '7':
            count = count + 1
    if count == len(str(num_ld)):
        print('YES')