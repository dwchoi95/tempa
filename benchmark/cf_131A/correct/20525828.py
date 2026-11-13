import string
S = input()
N = len(S)


def check1():
    for s in S:
        if s in string.ascii_lowercase:
            return False
    return True


def check2():
    if N == 1:
        return S[0] in string.ascii_lowercase
    else:
        if S[0] in string.ascii_lowercase:
            for s in S[1:]:
                if s in string.ascii_lowercase:
                    return False
            return True
        else:
            return False

ans = ""
if check1():
    for s in S:
        ans += s.lower()
elif check2():
    for i in range(N):
        if i == 0:
            ans += S[i].upper()
        else:
            ans += S[i].lower()
else:
    ans = S
print(ans)