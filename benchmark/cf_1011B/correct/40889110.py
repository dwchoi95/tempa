from collections import Counter

def _cal(arr, x):
    ans = 0
    for i in arr:
        ans += int(i/x)
    return ans

def main():
    n, m = [int(x) for x in input().split()]
    a = [int(x) for x in input().split()]
    if (n > m):
        print(0)
        return
    n_of_each_type = list(Counter(a).values())
    max_val = max(n_of_each_type)
    x = None
    for i in range(1, max_val + 1, 1):
        val = _cal(n_of_each_type, i)
        if (val >= n):
            x = i
    if (x): print(x)
    else: print(0)

main()