N = int(input())

def roundI(inch):
    if inch<=1:
        return 0
    return 1

feet = int(N/36)
fullinch = (N - (feet*36))//3

finalinch = fullinch + roundI(N-feet*36-fullinch*3)
if finalinch == 12:
    feet += 1
    finalinch = 0
    
print(feet,finalinch)