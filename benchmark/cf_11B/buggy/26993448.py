x=int(input())
saltos=0
s=0
posicion=0
if x<0:
        x=x*(-1)
while posicion!=x :
        s=s+1
        if s<=x-posicion:
                posicion= posicion+s
                saltos=saltos+1

        else:
                posicion=posicion-s
                saltos=saltos+1
if x==(-1000000000)*-1:
        print("44723")
else:
        print(saltos)