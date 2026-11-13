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
    for i in range(100, 0, -1):
        num = 0
        for c in order:
            num += int(c / i)
        if num >= n:
            best = i
            break
    print(int(best))