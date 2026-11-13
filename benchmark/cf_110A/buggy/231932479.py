if __name__ == "__main__":
    n = input()
    count = 0
    res = True
    
    for ch in n:
        if ch == "4" or ch == "7":
            count += 1
    print(count)
    for ch in str(count):
        if ch != "4" and ch != "7":
            res = False
            break
    
    if res:
        print("YES")
    else:
        print("NO")