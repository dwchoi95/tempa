def main():
    n, m = [int(x) for x in input().split()]
    types = [int(x) for x in input().split()]

    if n > m:
        print(0)
        return

    dt = {}
    for t in types:
        if t not in dt:
            dt[t] = 0

        dt[t] += 1

    sorted_items = sorted(dt.items(), key=lambda i: i[1], reverse=True)

    for i in range(sorted_items[0][1], 0, -1):
        n_count = 0
        for k, v in sorted_items:
            n_count += v // i
        if n_count >= n:
            print(i)
            return

    print(0)


if __name__ == '__main__':
    main()