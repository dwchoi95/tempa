# Main
def main():
    n, m = map(int, input().split())
    food = list(map(int, input().split()))

    arr = dict()
    for i in food:
        if i not in arr:
            arr[i] = 1
        else:
            arr[i] += 1
            
    maxD = 0
    for d in range(1, 101, 1):
        temp = arr
        k = 0
        flag = 0
        for key, val in temp.items():
            while val >= d:
                flag += 1
                k += 1
                val -= d
        if k >= n and d > maxD:
            maxD = d
        if flag == 0:
            break
        
    print(maxD)

# End main

if __name__ == "__main__":
    main()