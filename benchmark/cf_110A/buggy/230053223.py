n = int(input("Enter the number : "))
k = int( n % 10 )
u = 10
i = 10
m = 0
d = 0
# print ( k )
for x in range ( 1 , 20 ):
    if ( k == 4 ):
        m = m + 1
    elif (k == 7):
        d = d + 1
    n = int((n - k)/i)
    k = int (int((n/i))%10)
    # print(n)
    # print(k)
q = int(m + d) + 1
# print(q)
if ( q == 4):
    print("YES")
elif ( q == 7):
    print("YES")
else :
    print("NO")