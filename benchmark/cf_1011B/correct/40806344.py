nbParticipants, nbFood = map(int, input().split())

food = [int(i) for i in input().split()]
food.sort()


nb = [0 for i in range(100)]

for i in food:
   nb[i-1] += 1



for nbJours in range(1, 101):
    if sum([nb[i]//nbJours for i in range(100)]) < nbParticipants:
      maximum = nbJours-1
      break

    maximum = nbJours

print(maximum)