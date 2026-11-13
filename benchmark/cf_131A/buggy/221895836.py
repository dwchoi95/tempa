x = list(input())
i = len(x) - 1
while i >= 1:
    x[i] = x[i].lower()
    i = i - 1
string = ''.join([i for i in x])
print(string)