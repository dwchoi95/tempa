S = input()
if S.isupper() :
    print(S[0] + S[1:].lower())
elif (S[0].islower() and S[1:].isupper()):
    print(S[0].upper()+ S[1:].lower())
else:
    print(S)