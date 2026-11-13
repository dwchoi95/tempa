# LUOGU_RID: 121449233
n = int(input())

foot = n // 36
left = n - 36 * foot
inch = round(left / 3)

print("{} {}".format(foot,inch))