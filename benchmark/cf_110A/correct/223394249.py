def main():
    n = input()
    counter = 0
    i = 0
    while (i < len(n)):
        rest = int(n[i])
        if (rest == 4 or rest == 7):
            counter += 1
        i += 1
    if (counter == 4 or counter == 7):
        print('YES')
    else:
        print('NO')


if __name__ == '__main__':
    main()