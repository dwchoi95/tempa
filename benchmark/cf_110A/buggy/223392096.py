def main():
    n = int(input())
    while (n != 0):
        rest = n % 10
        #print('rest', rest)
        n  = int(n/ 10)
        if (rest != 4 and rest != 7):
            print('NO')
            return
    print('YES')

if __name__ == '__main__':
    main()