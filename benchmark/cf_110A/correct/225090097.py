def code(*args):
    
    number = args[0]
    count_of_lucky_number = 0
    
    while (number > 0):
        last_digit = number % 10
        if (last_digit == 4 or last_digit == 7):
            count_of_lucky_number += 1            
        number //= 10
    
    if (count_of_lucky_number == 4 or count_of_lucky_number == 7):
        return "YES"
    
    return "NO"


if __name__ == "__main__":
    # Take inputs here
    number = int(input())
    result = code(number)  # Pass arguments
    print(result)