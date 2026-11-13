nourinz=input()
nn=0
for n in nourinz:
    if  (int(n) ==4  ):
        nn=nn+1
    if(int(n) ==7):
        nn=nn+1
if (nn ==0):
    print('NO')
if(nn != 0):
    print('YES')