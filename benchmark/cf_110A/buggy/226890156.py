import sys

input = sys.stdin.readline

def in2i():
    '''
    input to int
    '''
    return int(input())

def in2il():
    '''
    intput to int list
    '''
    return (list(map(int, input().split())))

def s2cs():
    '''
    string to chars
    '''
    s = input()
    return (list(s[:len(s)]))

s = input()
count = 0
for c in s:
    if c == '4' or c == '7':
        count += 1
if count > 0 and (count % 4 == 0 or count % 7 == 0):
    print("YES")
else:
    print("NO")