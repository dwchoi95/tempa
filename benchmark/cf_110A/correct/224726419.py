# list(map(int,input().split()))
import sys
n=input()
import re
res=re.findall(r'[4|7]',n)
print('YES') if len(res)==4 or len(res)==7 else print('NO')