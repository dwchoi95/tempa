import random  
import heapq 
import math
from collections import Counter 
import sys
from fractions import gcd
sys.setrecursionlimit(300000)
from random import randrange
 
 
 
 
#########################################################################
 
# O(|m| log(max(m) + max(a)))
def chinese_remainder(m, a):
    '''
        m - modulos, a - coefficients (arrays)
        * m have to be mutually COPRIME *
    '''
    res, prod = 0, 1
    for m_i in m:
        prod *= m_i
    for m_i, a_i in zip(m, a):
        p = prod // m_i
        res += a_i * modinv(p, m_i) * p
    return res % prod
 
 
 
# O(log(a+b))
def egcd(a, b):
    ''' Extended Euclidian algorithm. '''
    if a == 0:
        return (b, 0, 1)
    else:
        g, y, x = egcd(b % a, a)
        return (g, x - (b // a) * y, y)
 
def modinv(a, m):
    ''' Finds modular inverse of a modulo m.  '''
    while a < 0:
        a += m
    g, x, y = egcd(a, m)
    if g != 1:
        raise Exception('Modular inverse does not exist')
    else:
        return x % m
 
#########################################################################
#########################################################################
 
def pi(n):
    ''' Returns two arrays pi1, pi2:
            pi1[i] = pi(i) for i <= sqrt(n)
            pi2[i] = pi(n // i) for i <= sqrt(n)
     '''
    lim = int(n**0.5)
    while lim*lim <= n: lim += 1
    lim -= 1
 
    pi1, pi2 = [0]*(lim + 1), [0]*(lim + 1)
    for i in range(1, lim + 1):
        pi1[i] = i - 1
        pi2[i] = n//i - 1
 
    for i in range(2, lim + 1):
        if pi1[i] == pi1[i - 1]:
            continue
        p = pi1[i - 1]
        for j in range(1, min(n // (i * i), lim) + 1):
            st = i * j
            if st <= lim:
                pi2[j] -= pi2[st] - p
            else:
                pi2[j] -= pi1[n // st] - p
        for j in range(lim, min(lim, i * i - 1), -1):
            pi1[j] -= pi1[j // i] - p
    return pi1, pi2
 
#########################################################################
#########################################################################
 
def num_of_divisors(n):
    nd = [0] * (n+1)
    for i in range(1, n+1):
        for j in range(i, n+1, i):
            nd[j] += 1
    return nd
 
 
def sum_of_divisors(n):
    sd = [0] * (n+1)
    for i in range(1, n+1):
        for j in range(i, n+1, i):
            sd[j] += i
    return sd
 
#########################################################################
def fast_prime_sieve(n):
    """
        Input n>=6, Returns a list of primes, 2 <= p <= n
        Taken from: https://stackoverflow.com/questions/2068372/fastest-way-to-list-all-primes-below-n/
    """
    n += 1
    n, correction = n-n%6+6, 2-(n%6>1)
    sieve = [True] * (n//3)
    for i in range(1,int(n**0.5)//3+1):
      if sieve[i]:
        k=3*i+1|1
        sieve[      k*k//3      ::2*k] = [False] * ((n//6-k*k//6-1)//k+1)
        sieve[k*(k-2*(i&1)+4)//3::2*k] = [False] * ((n//6-k*(k-2*(i&1)+4)//6-1)//k+1)
    return [2,3] + [3*i+1|1 for i in range(1,n//3-correction) if sieve[i]]
#########################################################################
 
def egcd(a, b):
    ''' Extended Euclidian algorithm. '''
    if a == 0:
        return (b, 0, 1)
    else:
        g, y, x = egcd(b % a, a)
        # x * a + y * b = g
        return (g, x - (b // a) * y, y)
 
_gcd = lambda a, b: a+b if a==0 or b==0 else gcd(b, a % b)
 
def gcd(a, b):
    if a==0 or b == 0:
        return a+b
    return gcd(b, a % b)
 
 
#########################################################################
 
''' Modular square root '''
 
 
#########################################################################
 
def legendre_symbol(a, p):
    ls = pow(a, (p - 1) // 2, p)
    return -1 if ls == p - 1 else ls
 
def modular_sqrt(a, p):
    if legendre_symbol(a, p) != 1:
        return 0
    elif a == 0:
        return 0
    elif p == 2:
        return 0
    elif p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    s = p - 1
    e = 0
    while s % 2 == 0:
        s //= 2
        e += 1
    n = 2
    while legendre_symbol(n, p) != -1:
        n += 1
    x = pow(a, (s + 1) // 2, p)
    b = pow(a, s, p)
    g = pow(n, s, p)
    r = e
 
    while True:
        t = b
        m = 0
        for m in range(r):
            if t == 1:
                break
            t = pow(t, 2, p)
 
        if m == 0:
            return x
        gs = pow(g, 2 ** (r - m - 1), p)
        g = (gs * gs) % p
        x = (x * gs) % p
        b = (b * g) % p
        r = m
 
#########################################################################
''' Euler"s totient function for a single number '''
 
 
#########################################################################
 
from functools import lru_cache
 
def factorize(n):
    factorization = set()
    while n > 1:
        for i in range(2, n + 1):
            if n % i == 0:
                n //= i
                factorization.add(i)
                break
    return factorization
 
@lru_cache(maxsize=None)
def phi(n):
    totient = n
    for p in factorize(n):
        totient -= totient//p
    return totient
 
#########################################################################
 
#########################################################################
 
def max_subarray(a):
    max_so_far = max_ending_here = 0
    for el in a:
        # in case a speed-up is required, change the below max/min to if-else statements.
        max_ending_here = max(0, max_ending_here + el)
        max_so_far = max(max_so_far, max_ending_here)
    return max_so_far
 
 
#########################################################################
 
 
#########################################################################
 
def maximum_xor(nums):
    answer = 0
    for i in range(31, -1, -1):
        answer <<= 1
        prefixes = {num >> i for num in nums}
        answer += any(answer^1^p in prefixes for p in prefixes)
    return answer
 
 
#########################################################################
 
'''
    Finds longest increasing subsequence in O(n log n) time.
'''
 
 
#########################################################################
 
def lis(a):
    p, m, l = [0]*len(a), [0]*(len(a) + 1), 0
    for i in range(len(a)):
       lo, hi = 1, l
       while lo <= hi:
           mid = (lo + hi)//2
           if a[m[mid]] < a[i]:
               lo = mid+1
           else:
               hi = mid-1
       p[i], m[lo] = m[lo-1], i
       if lo > l:
           l = lo
    s, k = [], m[l]
    for i in range(l-1, -1, -1):
        s.append(a[k])
        k = p[k]
    return s[::-1]
 
#########################################################################
#########################################################################
#########################################################################
def find_kth(arr, k, start=0, end=None):
    if not end:
        end = len(arr) -1
    pivot_ridx = randrange(start, end)
    pivot = arr[pivot_ridx]
    pivot_idx = _partition(arr, start, end, pivot_ridx)
    if pivot_idx + 1 == k:
        return pivot
    elif pivot_idx + 1 > k:
        return find_kth(arr, k, start, pivot_idx)
    else:
        return find_kth(arr, k, pivot_idx, end)
 
def _partition(arr, start, end, pivot_idx):
    pivot = arr[pivot_idx]
    arr[end], arr[pivot_idx] = arr[pivot_idx], arr[end]
    inc_idx = start
    for i in range(start, end):
        if arr[i] <= pivot:
            arr[inc_idx], arr[i] = arr[i], arr[inc_idx]
            inc_idx += 1
    arr[end], arr[inc_idx] = arr[inc_idx], arr[end]
    return inc_idx
#########################################################################
#########################################################################
 
def count_sort(a):
    mn, mx = float('inf'), -float('inf')
    for x in a:
        if x < mn: mn = x
        if x > mx: mx = x
    counter = [0 for _ in range(mx - mn + 1)]
    for x in a:
        counter[x - mn] += 1
    j = 0
    for i in range(mx - mn + 1):
        a[j:j+counter[i]] = [i + mn]*counter[i]
        j += counter[i]
 
 
#########################################################################
 
 
#########################################################################
 
 
 
def lcs(a, b):
    ''' Finds longest common subsequence of arrays a, b. '''
    lengths = [[0 for j in range(len(b) + 1)] for i in range(len(a) + 1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if x == y:
                lengths[i+1][j+1] = lengths[i][j] + 1
            else:
                lengths[i+1][j+1] = max(lengths[i+1][j], lengths[i][j+1])
    result = []
    x, y = len(a), len(b)
    while x != 0 and y != 0:
        if lengths[x][y] == lengths[x-1][y]:
            x -= 1
        elif lengths[x][y] == lengths[x][y-1]:
            y -= 1
        else:
            result.append(a[x-1])
            x, y = x - 1, y - 1
    return result[::-1]
 
 
#########################################################################
#########################################################################
def is_anagram(str1, str2): 
     return Counter(str1) == Counter(str2)
#########################################################################
#########################################################################
def power(x, y, p): 
    res = 1;  
    x = x % p;  
    while (y > 0): 
        if (y & 1): 
            res = (res * x) % p; 
        y = y>>1;
        x = (x * x) % p; 
    return res;
#########################################################################
def miillerTest(d, n): 
    a = 2 + random.randint(1, n - 4); 
    x = power(a, d, n); 
    if (x == 1 or x == n - 1): 
        return True; 
    while (d != n - 1): 
        x = (x * x) % n; 
        d *= 2; 
        if (x == 1): 
            return False; 
        if (x == n - 1): 
            return True; 
    return False; 
def isPrime( n, k): 
    if (n <= 1 or n == 4): 
        return False; 
    if (n <= 3): 
        return True; 
    d = n - 1; 
    while (d % 2 == 0): 
        d //= 2; 
    for i in range(k): 
        if (miillerTest(d, n) == False): 
            return False; 
  
    return True;
#########################################################################
#########################################################################
  
def gcd_list(li):
    return reduce(gcd,li)
  
'''
    Finds longest increasing subsequence in O(n log n) time.
'''


#########################################################################

def lis(a):
    p, m, l = [0]*len(a), [0]*(len(a) + 1), 0
    for i in range(len(a)):
       lo, hi = 1, l
       while lo <= hi:
           mid = (lo + hi)//2
           if a[m[mid]] < a[i]:
               lo = mid+1
           else:
               hi = mid-1
       p[i], m[lo] = m[lo-1], i
       if lo > l:
           l = lo
    s, k = [], m[l]
    for i in range(l-1, -1, -1):
        s.append(a[k])
        k = p[k]
    return s[::-1]

#########################################################################
 
# for _ in range(int(input())):
# input=open("input.txt","r").readline
n=int(input())
e=n//36
f=n%36
print(e,int(math.ceil(f/3)))
# if len(set(e))==1:
#     open("output.txt","w").write("YES")
# else:
#     open("output.txt","w").write("NO")