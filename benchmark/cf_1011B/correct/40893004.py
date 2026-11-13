'''
B. Planning The Expedition

Natasha is planning an expedition to Mars for n people. One of the important tasks is to provide food for each participant.

The warehouse has m daily food packages. Each package has some food type a_i.

Each participant must eat exactly one food package each day. Due to extreme loads, each participant must eat the same food type throughout the expedition. Different participants may eat different (or the same) types of food.

Formally, for each participant j Natasha should select his food type b_j and each day j-th participant will eat one food package of type b_j. The values b_j for different participants may be different.

What is the maximum possible number of days the expedition can last, following the requirements above?

Input
The first line contains two integers n and m (1 < n < 100, 1 < m < 100) — the number of the expedition participants and the number of the daily food packages available.
The second line contains sequence of integers a_1, a_2, \dots, a_m (1 < a_i < 100), where a_i is the type of i-th food package.

Output
Print the single integer — the number of days the expedition can last. If it is not possible to plan the expedition for even one day, print 0.

Tests
(In this directory), 'cf test 1011 B solution.py'
'''
import heapq
numPeople, numPackages = input().split(" ")
packages = input().split(" ")

packs = {}
for p in packages:
	if p not in packs:
		packs[p] = 1
	else:
		packs[p] += 1

ps = [(-v, 0, v) for (k, v) in packs.items()]
heapq.heapify(ps)

for i in range(0, int(numPeople)):
	top = heapq.heappop(ps)
	#print("calcing", top[2], "//", top[1] + 2)
	next_elem = (-(top[2] // (top[1] + 2)), top[1] + 1, top[2])
	heapq.heappush(ps, next_elem)
	#print(ps)	

#print(ps)
print(min([p[2] // p[1] for p in filter(lambda x: x[1] > 0, ps)]))