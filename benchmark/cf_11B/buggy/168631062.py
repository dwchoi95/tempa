x= int(input())
result="NO"
for n in range(2, x, 2):
    if ((n%2==0) and ((x-n)%2==0)):
        result="YES"
print(result)