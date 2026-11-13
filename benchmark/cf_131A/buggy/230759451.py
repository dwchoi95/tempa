S= input()
s=''
if (len(S))>1:
  if 'A'<=(S[::])<='Z':
    lower= (S[::]).lower()
    s+=lower
    print(s)
  elif 'a'<=S[0]<='z' and 'A'<=(S[1:])<='Z':
    upper= (S[0]).upper()
    s+=upper
    lower= (S[1:]).lower()
    s+=lower
    print(s)
  else:
    print(S)
else:
  upper= S.upper()
  s+=upper
  print(s)