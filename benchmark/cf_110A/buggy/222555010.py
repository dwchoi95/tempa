n = int(input())
s = str(n)
if '4' in s and '7' in s and not('1' in s or '2' in s or '3' in s or '5' in s or '6' in s or '8' in s or '9' in s or '0' in s):
    print("YES")
else:
    print("NO")