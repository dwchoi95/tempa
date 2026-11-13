def is_lucky(num):
    while num > 0:
        digit = num % 10
        if digit != 4 and digit != 7:
            return False
        num //= 10
    return True

def is_nearly_lucky(num):
    count = 0
    while num > 0:
        digit = num % 10
        if digit == 4 or digit == 7:
            count += 1
        num //= 10
    return is_lucky(count)

if __name__ == "__main__":
    n = int(input())
    if is_nearly_lucky(n):
        print("YES")
    else:
        print("NO")