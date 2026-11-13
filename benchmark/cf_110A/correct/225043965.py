def main():

    inp = input()

    IL = len(inp)

    LN = 0

    for i in range(0, IL):
        if inp[i] == "7" or inp[i] == "4":
            LN += 1
            
            continue
    
    if LN == 7 or LN == 4 or LN == 47 or LN == 74:
        print("YES")

    else:
        print("NO")

main()