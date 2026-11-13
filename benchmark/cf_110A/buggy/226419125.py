def is_almost_lucky(n):
    lucky_numbers = [4, 7, 44, 47, 74, 77, 444, 447, 474, 477, 744, 747, 774, 777]
    for num in lucky_numbers:
        if n % num == 0:
            return True
    return False

n = int(input())
if is_almost_lucky(n):
    print("YES")
else:
    print("NO")