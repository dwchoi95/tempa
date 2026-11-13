import sys
liczba = int(input())

strLiczba = str(liczba)
for i in range(len(strLiczba)):
    x = liczba % 10
    if x == 4 or x == 7:
        liczba = liczba // 10
    else:
        print("NO")
        sys.exit()
print("YES")