n=str(input())
n1=(list(n))

m=''
list1=['A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z']
list2=['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z']

for i in range(26):
    if(n1[0]==list2[i]):
        n1[0]=(list1[i])

for i in range(1,len(n)):
    for j in range(26):
        if(n1[i]==list1[j]):
            n1[i]=(list2[j])

for i in range(len(n1)):
    m+=n1[i]
print(m)