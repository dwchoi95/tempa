from collections import Counter

npar, npack = map(int, input().split())
pack_arr = list(map(int, input().split()))

if npar > npack:
    print(0)
elif npack//npar == 1:
    print(1)
else:
    occurences = Counter(pack_arr)
    longest_days = 1
    for days in range(2, npack//npar + 1):
        current_ful = 0
        for k in occurences:
            current_ful += occurences[k]//days
            if current_ful >= npar:
                longest_days = days
                break
        else:
            break
    print(longest_days)