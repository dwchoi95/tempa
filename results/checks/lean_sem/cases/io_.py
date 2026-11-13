import sys
n = int(input())
xs = list(map(int, sys.stdin.readline().split()))
rest = sys.stdin.read()
print(n, xs, repr(rest))
sys.stdout.write("w\n")
try:
    input()
except EOFError:
    print("eof")
print(1, 2, sep="-", end="!\n")
exit()
print("unreached")
