x=int(input())
saltos=0
s=0
posicion=0
if x<0:
        x=x*-1
while posicion!=x:
        saltos=saltos+1
        s=s+1
        if posicion<x and x-posicion>=s:
                posicion=posicion+s
        if posicion<x and x-posicion<s:
                posicion=posicion-s
print(saltos)