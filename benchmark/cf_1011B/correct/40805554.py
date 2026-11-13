men, food = map(lambda x: int(x), input().split())

types = map(lambda x: int(x), input().split())

food_dic = {}

for t in types:
	if t in food_dic:
		food_dic[t] += 1
	else:
		food_dic.update({t: 1})


food = list(food_dic.values())
food.sort(reverse=True)

if len(food) < men:
	food += [0]*(men - len(food))
else:
	food = food[:men]

type_list = [i+1 if food[i] > 0 else 0 for i in range(len(food))]


def get_same(type_list, max_i):
	res = []
	typ = type_list[max_i]
	for i in range(len(type_list)):
		if type_list[i] == typ:
			res.append(i)
	return res


while True:
	max_i = food.index(max(food))
	min_i = food.index(min(food))

	same_i = get_same(type_list, max_i)
	all_f = 0
	for i in same_i:
		all_f += food[i]

	# print(same_i)
	if all_f // (len(same_i) + 1) <= food[min_i]:
		break
	# print(all_f)
	type_list[min_i] = type_list[max_i]
	tru = all_f // (len(same_i) + 1)
	food[min_i] = tru
	for i in same_i:
		food[i] = tru
	for i in range(all_f % (len(same_i) + 1)):
		food[same_i[i]] += 1
	# print(food)

# print(food)
print(min(food))