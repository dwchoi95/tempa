n = input()
luckynumber = [lucky for lucky in n if lucky == '4' or lucky == '7']
if len(luckynumber) == '4' or len(luckynumber) == '7':
    print("YES")
else:
    print("NO")