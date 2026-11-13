number = list(int(digit) for digit in str(input()))
counter = 0
tag = "NO"
for num in number:
    if num == 4:
        counter += 1
    elif num == 7:
        counter += 1
number_set = list(int(set0) for set0 in str(counter))
for set1 in number_set:
    if int(set1) == 4:
        tag = "YES"
    elif int(set1) == 7:
        tag = "YES"
    else:
        tag = "NO"
print(tag)