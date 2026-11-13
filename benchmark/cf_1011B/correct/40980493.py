from collections import defaultdict

def planning_the_expedition():
    limit = 100
    
    n, m = map(int, input().split())
    
    food_types = [int(k) for k in input().split()]
    
    if m < n:
        return 0

    food_count = defaultdict(int)
    
    for f in food_types:
        food_count[f] += 1

    for day in range(limit,0,-1):
        fc = food_count.copy()
        k = 0

        for f_type in fc.keys():
            while fc[f_type] >= day:
                fc[f_type] -= day
                k += 1

        if k >= n:
            return day
    
    return 0
    
print(planning_the_expedition())