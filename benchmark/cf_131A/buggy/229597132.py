a=input()

if "a"<=a[0]<="z":
    x=ord(a[0])-32
    y=chr(x)
elif "A"<=a[0]<="Z":
    x=ord(a[0])
    y=chr(x)
print(y,end="")
for j in range(1,len(a)):
  if "A"<=a[j]<="Z":
    x=ord(a[j])+32
    y=chr(x)
    print(y,end="")
  else:
    print(a[j],end="")