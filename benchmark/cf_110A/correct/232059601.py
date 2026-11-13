from collections import Counter

counter = Counter({"lucky": 0, "unlucky": 0})
n = int(input())
k = str(n)

for letter in k:
    l = int(letter)
    if l == 4 or l == 7:
        counter['lucky'] += 1
    else:
        counter['unlucky'] += 1
        


print("YES" if counter["lucky"] == 4 or counter["lucky"] == 7 else "NO")