# https://codeforces.com/problemset/problem/131/A

word = input()
convert = True
i = 1
while i < len(word) and convert:
    if 'a' <= word[i] <= 'z':
        convert = False
    i += 1
if convert:
    print(word.capitalize())
else:
    print(word)