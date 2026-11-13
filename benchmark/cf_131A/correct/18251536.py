'''

def main():

    from sys import stdin,stdout

if __name__=='__main__':

    main()

'''

#1A

'''

def main():

    from sys import stdin,stdout

    from math import ceil

    n,m,a=map(int,stdin.readline().split())

    stdout.write(str(ceil(n/a)*ceil(m/a)))

if __name__=='__main__':

    main()

'''

#4A

'''

def main():

    from sys import stdin,stdout

    i=int(stdin.readline())

    if i&1:

        stdout.write('NO\n')

    else:

        if i//2 >1:

            stdout.write('YES\n')

        else:

            stdout.write('NO\n')

if __name__=='__main__':

    main()

'''

#71A

'''

def main():

    from sys import stdin,stdout

    for _ in range(int(stdin.readline())):

        s=stdin.readline().strip()

        if len(s) <=10:

            stdout.write(s+'\n')

        else:

            stdout.write(s[0]+str(len(s[1:-1]))+s[-1]+'\n')

if __name__=='__main__':

    main()

'''

#158A

'''

def main():

    from sys import stdin,stdout

    n,k=map(int,stdin.readline().split())

    a=list(map(int,stdin.readline().split()))

    count=0

    for i in range(n):

        if a[i] and a[i]>=a[k-1]:

            count+=1

    stdout.write(str(count))

if __name__=='__main__':

    main()

'''

#188A

'''

def main():

    from sys import stdin,stdout

    s=stdin.readline().strip()

    t=''

    s=s.lower()

    for i in s:

        if i not in 'aeiouy':

            t+='.'+i

    stdout.write(t)

if __name__=='__main__':

    main()

'''

#50A

'''

def main():

    from sys import stdin,stdout

    n,m=map(int,stdin.readline().split())

    stdout.write(str((n*m)//2))

if __name__=='__main__':

    main()

'''

#231A

'''

def main():

    from sys import stdin,stdout

    count=0

    for _ in range(int(stdin.readline())):

        if sum(list(map(int,stdin.readline().split())))>=2:

            count+=1

    stdout.write(str(count))

if __name__=='__main__':

    main()

'''

#282A

'''

def main():

    from sys import stdin,stdout

    x=0

    for _ in range(int(stdin.readline())):

        s=stdin.readline().strip()

        if '++' in s:

            x+=1

        elif '--' in s:

            x-=1

    stdout.write(str(x))

if __name__=='__main__':

    main()

'''

#158B



'''

def main():

    from sys import stdin,stdout

    n=int(stdin.readline())

    l=list(map(int,stdin.readline().split()))

    

    stdout.write(str(count))

if __name__=='__main__':

    main()

'''

#96A

'''

def main():

    from sys import stdin,stdout

    s=stdin.readline().strip()

    count=1

    flag=0

    for i in range(1,len(s)):

        if s[i]==s[i-1]:

            count+=1

            if count >=7:

                flag=1

                break

        else:

            count=1

    if flag:

        stdout.write('YES')

    else:

        stdout.write('NO')

if __name__=='__main__':

    main()

'''

#116A

'''

def main():

    from sys import stdin,stdout

    maxim=0

    total=0

    for _ in range(int(stdin.readline())):

        a,b=map(int,stdin.readline().split())

        total+=(b-a)

        if total >maxim:

            maxim=total

    stdout.write(str(maxim))

if __name__=='__main__':

    main()

'''

#112A

'''

def main():

    from sys import stdin,stdout

    s=stdin.readline().strip().lower()

    t=stdin.readline().strip().lower()

    if s==t:

        stdout.write('0')

    elif s < t:

        stdout.write('-1')

    else:

        stdout.write('1')

if __name__=='__main__':

    main()

'''

#339A

'''

def main():

    from sys import stdin,stdout

    l=list(map(str,stdin.readline().strip().split('+')))

    l.sort()

    stdout.write('+'.join(l))

if __name__=='__main__':

    main()

'''

#131A





def main():

    from sys import stdin,stdout

    s=stdin.readline().strip()

    if s.isupper():

        stdout.write(s.lower())

    elif (s[0].islower() and s[1:].isupper()) or (len(s)==1 and s.islower()):

        stdout.write(s.title())

    else:

        stdout.write(s)

if __name__=='__main__':

    main()



#266A

'''

def main():

    from sys import stdin,stdout

    n=int(stdin.readline())

    count=0

    s=stdin.readline().strip()

    for i in range(1,n):

        if s[i]==s[i-1]:

            count+=1

    stdout.write(str(count))

if __name__=='__main__':

    main()

'''

#133A

'''

def main():

    from sys import stdin,stdout

    s=stdin.readline().strip()

    if 'H' in s or 'Q' in s or '9' in s:

        stdout.write('YES')

    else:

        stdout.write('NO')

if __name__=='__main__':

    main()

'''

#281A

'''

def main():

    from sys import stdin,stdout

    s=stdin.readline().strip()

    stdout.write(s[0].upper()+s[1:])

if __name__=='__main__':

    main()

'''

#58A

'''

def main():

    from sys import stdin,stdout

    test='hello'

    s=stdin.readline().strip()

    while len(test) and len(s):

        if test[0]==s[0]:

            test=test[1:]

            s=s[1:]

        else:

            s=s[1:]

    if test=='':

        stdout.write('YES')

    else:

        stdout.write('NO')

if __name__=='__main__':

    main()

'''

#236A

'''

def main():

    from sys import stdin,stdout

    if len(set(stdin.readline().strip())) & 1:

        stdout.write('IGNORE HIM!')

    else:

        stdout.write('CHAT WITH HER!')

if __name__=='__main__':

    main()

'''

#467A

'''

def main():

    from sys import stdin,stdout

    count=0

    for _ in range(int(stdin.readline())):

        a,b=map(int,stdin.readline().split())

        if b-a>=2:

            count+=1

    stdout.write(str(count))

if __name__=='__main__':

    main()

'''

#148A

'''

def main():

    from sys import stdin,stdout

    k=int(stdin.readline())

    l=int(stdin.readline())

    m=int(stdin.readline())

    n=int(stdin.readline())

    d=int(stdin.readline())

    count=0

    for i in range(1,d+1):

        if i % k and i % l and i % m and i % n:

            count+=1

    stdout.write(str(d-count))

if __name__=='__main__':

    main()

'''

#263A

'''

def main():

    from sys import stdin,stdout

    for i in range(5):

        a=list(map(int,stdin.readline().split()))

        try:

            x=a.index(1)+1

            y=i+1

        except:

            g=''

    stdout.write(str(abs(x-3)+abs(y-3)))

if __name__=='__main__':

    main()

'''

#546A

'''

def main():

    from sys import stdin,stdout

    k,n,w=map(int,stdin.readline().split())

    m=(w*(w+1)*k)//2

    if m<=n:

        stdout.write('0')

    else:

        stdout.write(str(m-n))

if __name__=='__main__':

    main()

'''

#136A

'''

def main():

    from sys import stdin,stdout

    n=int(stdin.readline())

    l=list(map(int,stdin.readline().split()))

    p=[0 for _ in range(n)]

    for i in range(n):

        p[l[i]-1]=i+1

    stdout.write(' '.join(str(x) for x in p))

if __name__=='__main__':

    main()

'''

#122A

'''

def main():

    l=[]

    for i in range(4,1001):

        s=str(i)

        flag=1

        for element in s:

            if element !='4' and element !='7':

                flag=0

                break

        if flag:

            l.append(i)

    from sys import stdin,stdout

    n=int(stdin.readline())

    for i in l:

        if n%i==0:

            stdout.write('YES')

            return

    stdout.write('NO')

if __name__=='__main__':

    main()

'''

#266B

'''

def main():

    from sys import stdin,stdout

    n,x=map(int,stdin.readline().split())

    s=stdin.readline().strip()

    for _ in range(x):

        s=s.replace('BG','GB')

    stdout.write(s)

if __name__=='__main__':

    main()

'''

#271A

'''

def main():

    from sys import stdin,stdout

    n=int(stdin.readline())

    n+=1

    while True:

        if len(str(n))==len(set(str(n))):

            break

        else:

            n+=1

    stdout.write(str(n))

if __name__=='__main__':

    main()

'''

#41A

'''

def main():

    from sys import stdin,stdout

    a=stdin.readline().strip()

    b=stdin.readline().strip()

    if a==b[-1::-1]:

        stdout.write('YES')

    else:

        stdout.write('NO')

if __name__=='__main__':

    main()

'''