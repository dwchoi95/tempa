word=input()
b=0
for w in word:
    if (w=='4' or w=='7'):
      b+=1
if b==len(word):
    print('YES')
else:
    print('NO')