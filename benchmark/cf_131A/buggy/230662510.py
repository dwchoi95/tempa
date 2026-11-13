s = str(input())
isAllUpperCase = 1
printed = 0

for i, item in enumerate(s):
    if s.isupper():
        print(s[0].lower() + s[1:].lower())
        printed = 1
        break
    if i == 0 and printed == 0:
        if item.islower():
            
            for j in range(i+1,len(s)):
                if s[j].islower():
                    isAllUpperCase = 0
                    break
        if isAllUpperCase == 1:
            print(s[0].upper()+s[1:].lower())
            printed = 1
            break

    if s[0].isupper() and s[1:].islower() and printed == 0:
        print(s)
        break