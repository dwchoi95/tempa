"""110A - Почти счастливое число """

def checkN(n):
    strN = str(n)
    without_47 = strN.replace("4", "").replace("7", "")
    if without_47 == 0:
        return "YES"
    delta = len(strN) - len(without_47)
    if delta == 4 or delta == 7:
        return "YES"
    return "NO"

n = int(input())

print(checkN(n))