def is_nearly_lucky(n):
  count = 0
  while n > 0:
    if n % 10 == 4 or n % 10 == 7:
      count += 1
    n //= 10
  return count in (4, 7)

if __name__ == "__main__":
  n = int(input())
  print("YES" if is_nearly_lucky(n) else "NO")