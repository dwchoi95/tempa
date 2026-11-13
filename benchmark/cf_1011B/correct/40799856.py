def main():
    n,m = [int(x) for x in input().split()]
    a = [int(x) for x in input().split()]
    count = [0]*101
    for i in a:
        count[i] += 1
    b = [(count[i],i) for i in range(1,101) if count[i]]
    b.sort(reverse=True)
    b = b[:n]
    flag = 0
    for i in b:
        flag += i[0]
    if m < n or flag < n:
        print(0)
    else:
        for day in range(1,102):
            people = 0
            for food,foodtype in b:
                people += food//day
            if people < n:
                break
        print(day-1)


if __name__ == '__main__':
    main()