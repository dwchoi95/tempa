nourinz=input()
zz=0
if((('4' in nourinz)and('7' in nourinz))==True):
   for n in nourinz:
         if  (int(n) ==4 or int(n) ==7 ):
                zz=zz+1
if ((zz==len(nourinz))):
    print('YES')
else:
    print('NO')