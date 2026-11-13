n = input()
lt = sum(1 for digit in n if digit in '47')
if lt in {4, 7}:
    print("YES")
else:
    print("NO")