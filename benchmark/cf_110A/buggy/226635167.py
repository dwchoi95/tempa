def generate_lucky_string(n):
    result = ""
    current_letter = 'a'
    lucky = [4, 7]

    while len(result) < n:
        result += current_letter
        current_letter = chr(ord(current_letter) + 1)

        if len(result) > 1:
            diff = abs(ord(result[-1]) - ord(result[-2]))
            if diff not in lucky:
                current_letter = chr(ord(current_letter) - 1)

    return result
n = int(input())
print(generate_lucky_string(n))