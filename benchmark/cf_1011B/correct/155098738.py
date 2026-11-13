def produs_cifre(numar):
 
 produs=1
 for i in numar:
  produs=produs*int(i)
 return (produs)
 
#def prime_generator(nr_elemente_prime):
 
 #vector_prime=[-1]*nr_elemente_prime
 #vector_rasp=[0]*nr_elemente_prime
 
 #vector_prime[1]=1
 
 #vector_rasp[1]=1
#primes sieve 
 #contor=2
 
 #for i in range(2,nr_elemente_prime):
 # if vector_prime[i]==-1:
 #  vector_prime[i]=1
 #  vector_rasp[contor]=i
 #  contor=contor+1
 # for j in range(i+i,nr_elemente_prime,i):
   # if vector_prime[j]==-1:
   #  vector_prime[j]=i
   #print(i,j) 
 
# my_set=set(vector_rasp)
 #my_set.remove(0)
 #my_set.remove(1)
 
 #lista_prime=list(my_set)
 #lista_prime.sort()
 #return my_set


def functie(nodul,vectorul,cate,culori,vizitat):
 #print(noi_culori)
 if vizitat[nodul]==0:
  vizitat[nodul]=1
  
  
  if culori[nodul-1]!=noi_culori[nodul-1]:
   #print(nodul)
   cate[0]=1+cate[0]
   noi_culori[nodul-1]=culori[nodul-1]
  
    
  for j in vectorul[nodul]:
    if vizitat[j]==0:
     noi_culori[j-1]=culori[nodul-1]
     functie(j,vectorul,cate,culori,vizitat)
     
 return(sum(cate))



#z=int(input())
for contor in range(0,1):
 #n,k
 n,m=list(map(int,input().split()))
 #n=int(input())
 
 lista=list(map(int,input().split()))
 vector=[0]*101

 
 for i in lista:
  vector[i]+=1
  
 answ=0
 
 
 for posibil in range(100,-1,-1):
  cati=0
  for j in range(100,-1,-1):
   if posibil>0:
    cati+=vector[j]//posibil
 
  if cati>=n :
   answ=max(answ,posibil)
   
 print(answ)