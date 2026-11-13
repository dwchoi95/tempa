def f(n, order, i):
    num = 0
    for c in order:
        num += int(c / i)
    if num >= n:
        return True
    return False


if __name__ == "__main__":
    n, m = map(int, input().split(" "))
    inputs = list(map(int, input().split(" ")))
    l = [0] * 100
    for i in inputs:
        l[i - 1] += 1
    order = []
    for i in range(100):
        if l[i] != 0:
            order.append(l[i])
    # print(order)
    best = 0
    minn = 1
    maxx = sum(order)+1
    while minn != maxx:
        middle = int((minn + maxx) / 2)
        if f(n, order, middle):
            best = middle
            minn = middle + 1
        else:
            maxx = middle
    print(int(best))