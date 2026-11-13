def dliny(number):
    return ((number + 1) // 3) // 12, ((number + 1) // 3) % 12


print(*dliny(int(input())))