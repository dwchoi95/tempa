#0(1)
def is_nearly_lucky(suerte):
  count = 0
  while suerte > 0:
    if suerte% 10 == 4 or suerte% 10 == 7:
      count += 1
    suerte//= 10
  return count in (4, 7)

if __name__ == "__main__":
  suerte= int(input())
  print("YES" if is_nearly_lucky(suerte) else "NO")