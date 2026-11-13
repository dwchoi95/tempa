def change(b):
    if "a" <= b <= "z":
        return chr(ord(b) - ord('a') + ord('A'))
    else:
        return chr(ord(b) - ord('A') + ord('a'))
a = input()
A1 = {chr(i):0 for i in range(ord("a"), ord("z") + 1)}
A2 = {chr(i):0 for i in range(ord("A"), ord("Z") + 1)}
if len(a) == 1:
    if "a" <= a[0] <= "z":
        print(chr(ord(a[0]) - ord('a') + ord('A')))
    else:
        print(chr(ord(a[0]) + ord('a') - ord('A')))
else:
    for i in range(len(a)):
        if 'a' <= a[i] <= 'z':
            A1[a[i]] += 1
        elif 'A' <= a[i] <= 'Z':
            A2[a[i]] += 1
    A11 = list(A1.values())
    A22 = list(A2.values())
    if sum(A11) == 1 and sum(A22) == len(a) -1 or sum(A22) == len(a):
        for i in range(len(a)):
            print(change(a[i]), end = "")
    else:
        print(a)