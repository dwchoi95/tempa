numbers = input()

if len(numbers)<4:
    print('NO')
else:
    luckyNumbers=0

    for number in numbers:
        if number == '4' or number=='7':
            luckyNumbers+=1
            
    if luckyNumbers==7 or luckyNumbers==4:
        print('YES')
    else:
        print('NO')