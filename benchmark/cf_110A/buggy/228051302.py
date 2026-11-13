def nearly_lucky():
  c1, c2 = 0, 0

  for n1 in input():
    if n1 in '47': c1 += 1

  for n2 in str(c1):
    if n2 in '47': c2 += 2

  for n3 in str(c2):
    if n3 not in '47': return 'NO'

  return 'YES'

print(nearly_lucky())