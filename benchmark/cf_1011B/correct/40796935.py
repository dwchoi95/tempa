def solve(n, m, arr):
    fp = [0] * 105

    for t in arr:
        fp[t] += 1

    msf = 0
    for d in range(1, 101):
        count = 0
        for t in fp:
            count += t // d
        if count < n:
            continue
        msf = max(msf, d)
    return msf


def main():
    n, m = [int(x) for x in input().strip().split()]
    arr = [int(x) for x in input().strip().split()]
    print(solve(n, m, arr))


if __name__ == '__main__':
    main()