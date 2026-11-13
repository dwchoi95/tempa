import re, os, random
from queue import PriorityQueue
from collections import OrderedDict, Counter
print(re.findall(r'[4|7]', "4774a7"), re.findall(r'^[a-z]?[A-Z]+', "hELLO"), re.findall(r'^[A-Z][a-z]+', "Hello"))
print(bool(re.search(r'^[a-z][A-Z]$', "aB")), re.search(r'^[A-Z]$', "ab"), re.findall(r'\d+', "a12b345"))
m = re.search(r'[0-9]{2,3}', "ab1234"); print(m.group(), m.start(), m.end(), m.span())
print(re.sub(r'[aeiou]', '', "programming"), re.fullmatch(r'[a-z]*', "abc") is not None, re.match(r'b', "abc"))
tab = {ord("4"): None, ord("7"): None}
print("a4b7".translate(tab), "abc".translate(str.maketrans("ab", "xy")))
print(list(filter((3).__ne__, [3, 1, 3, 2])), (5).__add__(2), "ab".__len__(), [1, 2].__contains__(2))
print(list[0], dict[str, int], list(OrderedDict.fromkeys([3, 1, 3])), list(dict.fromkeys([2, 2, 1])))
print(Counter([1, 1, 2]).values(), {1: 2}.keys(), {1: 2}.items())
q = PriorityQueue(); q.put((2, "b")); q.put((1, "a")); print(q.get(), q.queue, q.empty())
print(range(10)[2:8:2], range(1, 20, 3)[::-1], list(range(10)[-3:]))
print({"b", "a", "c"} == {"a", "b", "c"}, sorted({"x", "y"}), len({("M", 1), ("F", 2)}))
