string = str(input())
string2 = ''
count = 0
for i in range(len(string)):
    if string[i].isupper() == True:
        count += 1
if count == len(string) or (count == (len(string) - 1) and string[0].islower() == True):
    string2 = string[0].upper() + string[1:].lower()
    print(string2)
else:
    print(string)

# Sat Oct 21 2023 16:09:13 GMT+0300 (Moscow Standard Time)