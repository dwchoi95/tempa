s=input()

l=len(s)

if l==1:

    if ord(s[0])>=65 and ord(s[0])<=90:

        print(chr(ord(s[0])-65+97),end='')

    else:

        print(chr(ord(s[0])+65-97),end='')

else:

    #print(s[0],end='')

    cnt=0

    for i in range(1,l):

        if ord(s[i])>=65 and ord(s[i])<=90:

            cnt+=1

    if cnt==l-1:

        if ord(s[0])>=65 and ord(s[0])<=90:

            print(chr(ord(s[0])-65+97),end='')

        else:

            print(chr(ord(s[0])+65-97),end='')

        for i in range(1,l):

            print(s[i].lower(),end='')

    else:

        print(s)