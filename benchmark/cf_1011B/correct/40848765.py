n, m = map(int, input().split())
provision = []
freq_dict = {}
for suit in map(int, input().split()):
    freq_dict[suit] = freq_dict.get(suit, 0) + 1
for suit in freq_dict:
    provision.append(freq_dict[suit])
provision.sort(reverse=True)
max_term = m // n
full_people = n
i = max_term
while i > 0 and full_people > 0:
    full_people = n
    for food in provision:
        full_people -= (food // i)
    i -= 1
if full_people <= 0:
    print(i + 1)
else:
    print(0)