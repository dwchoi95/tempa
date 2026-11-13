n=int(input())
s=str(n)
for ele in s:
    if ele=="4" or ele=="7":continue
    else:
        print("no")
        break
else:print("yes")