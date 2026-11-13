def is_lucky_digit(digit):
    return digit == '4' or digit == '7'

def count_lucky_digits(number):
    return sum(1 for digit in str(number) if is_lucky_digit(digit))

def is_nearly_lucky(number):
    lucky_digit_count = count_lucky_digits(number)
    return is_lucky_digit(lucky_digit_count)

def main():
    n = int(input("Enter the number (1 to 10^18): "))
    
    if is_nearly_lucky(n):
        print("YES")
    else:
        print("NO")

if __name__ == "__main__":
    main()