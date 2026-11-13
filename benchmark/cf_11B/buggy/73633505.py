#!/usr/bin/env python

def findJumps (dest, jumps, l, maxHops) :
    if (len(l) > maxHops) :
        return []
    if (dest == sum(l)) :
        return l

    l1 = l[:]
    l2 = l[:]
    l1.append(jumps + 1)
    l2.append(-(jumps + 1))

    ret = findJumps (dest, jumps + 1, l1, maxHops)
    if (len(ret) > 0) :
        return ret
    return findJumps (dest, jumps + 1, l2, maxHops)

maxHops = 5
def findShortest (dest) :
    for hop in range(1, maxHops) :
        result = findJumps(dest, 0, [], hop)
        if (len(result) > 0) :
            return result
    ## could not find a result even after trying upto maxHops
    return []
    
dest = int(input())
print(len(findShortest(dest)))