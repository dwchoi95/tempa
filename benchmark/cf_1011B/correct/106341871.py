def solve(particpant,package,seq) :
    maximumDays = package//particpant
    seq.sort()
    while maximumDays > 0  :
        participantFed = 0
        type = seq[0]
        temp = 0
        for x in seq :
            if temp == maximumDays :
                participantFed += 1
                temp = 1
                type = x
            else :
                if type == x :
                    temp += 1
                else :
                    type = x
                    temp = 1
        
        if temp == maximumDays :
            participantFed += 1
        
        if participantFed >= particpant :
            return maximumDays
       
        maximumDays -= 1
    
    return maximumDays
    

p,pa = list(map(int,input().split()))
seq = list(map(int,input().split()))

print (solve(p,pa,seq))