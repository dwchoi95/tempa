nourinz=input()
zz=0
for n in nourinz:
    if  (int(n) ==4 or int(n) ==7 ):
         zz=zz+1
if ((zz==4 or zz==7)):
    print('YES')
else:
    print('NO')