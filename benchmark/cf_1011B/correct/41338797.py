from collections import Counter
n, m = map(int, input().split())
tab = list(map(int, input().split()))
tab = Counter(tab).values()
#print(tab)
wynik = 1
while sum(paczka // wynik for paczka in tab) >= n:
    wynik += 1
print(wynik - 1)