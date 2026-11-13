s1=input()
se1=set(s1)
s2=s1.upper()
se2=set(s2)
if len(s1)==1:
    print(s1.swapcase())
if se1==se2:
    s3=s1.lower()
    print(s3)
else:
    se3=set(s1[1:len(s1)])
    se4=set(s2[1:len(s2)])
    if se3==se4:
        print(s1.swapcase())
    else:
        print(s1)