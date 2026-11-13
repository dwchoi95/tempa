S = input()
Capital = True
for C in S:
    if not C.isupper():
        Capital = False
        break
if Capital or (S[0].isupper() and S[1:] == S[1:].lower()):
    S = S.lower()
print(S)