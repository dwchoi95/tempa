def check(ptes, qtd_pessoas, dias):
    if(dias == 0):
       return False
    
    for tipo in ptes:
        k = ptes[tipo] // dias
        qtd_pessoas = qtd_pessoas - k
        if(qtd_pessoas == 0):
            break
            
    if(qtd_pessoas == 0): return True
    else: return False


def busca(palpites, pacotes, qtd_pessoas, left, right):
    if left == right:
        if check(pacotes, qtd_pessoas, left):
            return left
        else:
            return 0
    mid = ((left + right) // 2)

    if check(pacotes, qtd_pessoas, mid):
        return busca(palpites, pacotes, qtd_pessoas, mid+1 , right)
    else:
        return busca(palpites, pacotes, qtd_pessoas, left, mid)


l = input().split()
n = int(l[0])
m = int(l[1])
a = list(map(int, input().split()))

palpites = [0] * 101
for i in range(101):
    palpites[i] = i

# print(a)

if (n > m):
    print(0)
elif (n == m):
    print(1)
else:
    a.sort()
    trys = m // n
    aux = a[0]
    types = {}
    count = 1
    for i in range(1, m, 1):
        if a[i] == aux:
            count = count + 1
        else:
            types[aux] = count
            aux = a[i]
            count = 1
        if i == m - 1:
            types[aux] = count
    print(busca(palpites, types, n, 0, trys))