n = input()
lucky = False
if "4" in n:
    for i in range(len(n)):
        if n[i] == "4" or n[i] == "7":
            lucky = True

        else:
            print("NO")
            lucky = False
            break
    if lucky:
        print("YES")
else:
    print("NO")