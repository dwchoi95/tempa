# https://codeforces.com/problemset/problem/1011/B

import fileinput
import sys
from typing import List, Dict


def can_be_achived(paricipants: int, days: int, foods: List[int]) -> bool:
    if days == 0:
        return True

    max_participants = 0
    for food_t_q in foods:
        max_participants += (food_t_q // days)
    return paricipants <= max_participants


paricipants, food_types = None, None
powers: List[int]
for i, line in enumerate(fileinput.input()):
    if i == 0:
        paricipants, _ = [int(v) for v in line[:-1].split()]
    if i == 1:
        food_types = [int(v) for v in line[:-1].split()]
        break

f_q = {}
for food_t in food_types:
    if food_t in f_q:
        f_q[food_t] += 1
    else:
        f_q[food_t] = 1

food_quantity = [num for _, num in f_q.items()]

inf_days, sup_days = 0, paricipants
while inf_days < sup_days:
    s = (inf_days + sup_days + 1) // 2
    if can_be_achived(paricipants, s, food_quantity):
        inf_days = s
        if s == 0:
            break
    else:
        sup_days = s - 1

assert(inf_days == 0 or inf_days == sup_days)
print(inf_days)