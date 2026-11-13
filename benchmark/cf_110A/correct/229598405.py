def is_nearly_lucky(n):
  count = str(n).count('4') + str(n).count('7')
  return count in [4, 7]

n = int(input())
result = "YES" if is_nearly_lucky(n) else "NO"
print(result)